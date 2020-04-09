using Sockets

"""
    @msg(expression)

Calls `msg` with the name of the top-level function in `expression` as the first
argument and the arguments of that function as the remaining arguments. Note that
the toplevel function call will *not* be evaluated.

Example:
`@msg(sin(3))` will call `msg("sin", 3)`, i.e.
```
macroexpand(:(Atom.@msg(sin(3)))) == :((Atom.msg)("sin",3))
```
"""
macro msg(ex)
  @capture(ex, f_(args__)) || error("@msg requires function call syntax")
  :(msg($(string(f)), $(map(esc, args)...)))
end

"""
    @rpc(expression)

Calls `rpc` with the name of the top-level function in `expression` as the first
argument and the arguments of that function as the remaining arguments. Note that
the toplevel function call will *not* be evaluated.

Example:
`@rpc(sin(3))` will call `rpc("sin", 3)`, i.e.
```
macroexpand(:(Atom.@rpc(sin(3)))) == :((Atom.rpc)("sin",3))
```
"""
macro rpc(ex)
  @capture(ex, f_(args__)) || error("@rpc requires function call syntax")
  :(rpc($(string(f)), $(map(esc, args)...)))
end

"""
    sock

Socket over which the communication between server and client happens. Initialized
by `serve`.
"""
global sock = nothing

isactive(sock::Nothing) = false

"""
    isactive(sock)

Check whether the socked `sock` exists and is open.
"""
isactive(sock) = isopen(sock)

"""
    @ierrs(expression)

Catches errors internal to Atom.jl and renders them in the client.
"""
macro ierrs(ex)
  :(try
      $(esc(ex))
    catch e
      if !(e isa InterruptException)
        ee = EvalError(e, stacktrace(catch_backtrace()))
        Atom.msg("error", Dict(:msg         => "Julia Client – Internal Error",
                               :detail      => string(ee),
                               :dismissable => true))
      end
      nothing
    end)
end

"""
    initialise(; welcome = false)

Sets up the environment for Atom.jl: Stop `SIGINT`s from killing Julia and send
a welcome message to Atom if `welcome == true`.
"""
function initialise(; welcome = false)
  Juno.isprecompiling() && return
  Juno.setactive!(true)
  # exit_on_sigint(false)
  welcome && @msg welcome()
end

exit_on_sigint(on) = ccall(:jl_exit_on_sigint, Nothing, (Cint,), on)

"""
    serve(port; kws...)

Start an asynchronous Julia server that listens on `localhost:port` and handle
the messages sent over that socket. The `kws...` are passed through to `initialise`.
"""
function serve(port; kws...)
  server = listen(ip"127.0.0.1", port)
  print(stderr, "juno-msg-ready")
  global sock = accept(server)
  @async while isopen(sock)
    @ierrs let
      msg = JSON.parse(sock)
      @async @ierrs handlemsg(msg...)
    end
  end
  initialise(; kws...)
end

function connect(host, port; kws...)
  global sock = Sockets.connect(host, port)
  @async while isopen(sock)
    @ierrs let
      msg = JSON.parse(sock)
      @async @ierrs handlemsg(msg...)
    end
  end
  initialise(; kws...)
end

connect(port; kws...) = connect(ip"127.0.0.1", port; kws...)

"""
    msg(typ, args...)

Prints a json string to `sock` that contains all function arguments in an array.
"""
function msg(t, args...)
  isactive(sock) || return
  println(sock, json(c(t, args...)))
end

const handlers = Dict{String, Function}()

"""
    handle(func, typ)

Set the handler for messages of type `typ` to `func`.
"""
handle(f, t) = handlers[t] = f

id = 0
const callbacks = Dict{Int,Condition}()

"""
    rpc(typ, args...)

Sends a message to `sock` via `msg`. Blocks until the client returns a message
(which needs to send back the `callback` field).
"""
function rpc(t, args...)
  i, c = (global id += 1), Condition()
  callbacks[i] = c
  msg(d(:type => t, :callback => i), args...)
  return wait(c)
end

"""
    handlemsg(typ, args...)

Tries to call the message handler corresponding to `typ` (which can be set with
`handle`).
"""
function handlemsg(t, args...)
  callback = nothing
  isa(t, AbstractDict) && ((t, callback) = (t["type"], t["callback"]))
  if haskey(handlers, t)
    try
      result = handlers[t](args...)
      isa(callback, Integer) && msg("cb", callback, result)
    catch e
      isa(callback, Integer) && msg("cancelCallback", callback, string(e))
      rethrow()
    end
  else
    @warn("""
      Atom.jl: unrecognised message `$t`.
      Please make sure your Atom and Julia packages are in sync.
        - Try `using Pkg; Pkg.update()` to update this package.
        - Check for `julia-client` updates in Atom.
      """, _id=t, maxlog=1)
    callback ≠ nothing && msg("cancelCallback", callback)
  end
end

handle("cb") do id, result
  notify(callbacks[id], result)
  delete!(callbacks, id)
end

handle(() -> nothing, "junorc")

isconnected() = sock ≠ nothing && isopen(sock)

# communication utilities
# -----------------------

"""
    @tojs ex

Easy constructor of `Dict` or `NamedTuple`. The result is supposed
 to be parsed into JSON and send to a client over [`sock`](@ref).

## Examples

`ex`:
- will be transformed into `NamedTuple` with parentheses: `@tojs (k: v)` is `((k = v,))`
- will be transformed into `Dict` with braces: `@tojs {k: v}` is `Dict(:k => v)`
- will be transformed into `NamedTuple` without parentheses and brances: `@tojs k: v` is `((k = v,))`
- supports multiple property specs: `@tojs {k1: v1, k2: v2, ...}` is `Dict(:k1 => v1, :k2 => v2)`
- supports [JS-like shorthand property notation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Object_initializer): `@tojs sym` is `((sym = sym,))`
- can accept `=` instead of `:` notation: `@tojs {k = v}` is `@tojs {k: v}`
"""
macro tojs(ex)
  if ex isa Symbol || (@capture(ex, k_:v_) || @capture(ex, k_=v_))
    ex = Expr(:tuple, ex)
  end
  @assert isexpr(ex, :tuple, :braces) "@tojs expects braces for NamedTuple and parenthesis for Dict"
  k2vmap = map(ex.args) do x
    x isa Symbol && return (x, x)
    @assert (@capture(x, k_:v_) || @capture(x, k_=v_)) """
    @tojs expects a `key: val`, `key = val` or shorthand `sym` notation
    for object property specification, but got `$x`.
    """
    return (k, v)
  end
  return if ex.head === :tuple
    Expr(:tuple, map(((k,v),)->:($k=$v), k2vmap)...)
  else
    callargs = map(k2vmap) do (k,v)
      k = QuoteNode(k)
      :($k => $v)
    end
    Expr(:call, :Dict, callargs...)
  end |> esc
end

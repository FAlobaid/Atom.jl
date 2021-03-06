# This file is mostly generated by `scripts/generate_precompile.jl`

const __bodyfunction__ = Dict{Method,Any}()

# Find keyword "body functions" (the function that contains the body
# as written by the developer, called after all missing keyword-arguments
# have been assigned values), in a manner that doesn't depend on
# gensymmed names.
# `mnokw` is the method that gets called when you invoke it without
# supplying any keywords.
function __lookup_kwbody__(mnokw::Method)
    function getsym(arg)
        isa(arg, Symbol) && return arg
        @assert isa(arg, GlobalRef)
        return arg.name
    end

    f = get(__bodyfunction__, mnokw, nothing)
    if f === nothing
        fmod = mnokw.module
        # The lowered code for `mnokw` should look like
        #   %1 = mkw(kwvalues..., #self#, args...)
        #        return %1
        # where `mkw` is the name of the "active" keyword body-function.
        ast = Base.uncompressed_ast(mnokw)
        if isa(ast, Core.CodeInfo) && length(ast.code) >= 2
            callexpr = ast.code[end-1]
            if isa(callexpr, Expr) && callexpr.head == :call
                fsym = callexpr.args[1]
                if isa(fsym, Symbol)
                    f = getfield(fmod, fsym)
                elseif isa(fsym, GlobalRef)
                    if fsym.mod === Core && fsym.name === :_apply
                        f = getfield(mnokw.module, getsym(callexpr.args[2]))
                    elseif fsym.mod === Core && fsym.name === :_apply_iterate
                        f = getfield(mnokw.module, getsym(callexpr.args[3]))
                    else
                        f = getfield(fsym.mod, fsym.name)
                    end
                else
                    f = missing
                end
            else
                f = missing
            end
        else
            f = missing
        end
        __bodyfunction__[mnokw] = f
    end
    return f
end

function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing
    try; isdefined(Atom, Symbol("#115#116")) && precompile(Tuple{getfield(Atom, Symbol("#115#116")),Array{Any,1}}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#121#122")) && precompile(Tuple{getfield(Atom, Symbol("#121#122")),Hiccup.Node{:table}}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#121#122")) && precompile(Tuple{getfield(Atom, Symbol("#121#122")),Juno.Model}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#129#130")) && precompile(Tuple{getfield(Atom, Symbol("#129#130")),Text{String}}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#188#189")) && precompile(Tuple{getfield(Atom, Symbol("#188#189"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#195#200")) && precompile(Tuple{getfield(Atom, Symbol("#195#200"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#196#201")) && precompile(Tuple{getfield(Atom, Symbol("#196#201"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#208#213")) && precompile(Tuple{getfield(Atom, Symbol("#208#213"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#222#227")) && precompile(Tuple{getfield(Atom, Symbol("#222#227"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#230#231")) && precompile(Tuple{getfield(Atom, Symbol("#230#231")),Base.MethodList}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#230#231")) && precompile(Tuple{getfield(Atom, Symbol("#230#231")),MD}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.DictCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.FieldCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.KeywordCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.MethodCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.ModuleCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.PathCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#283#285")) && precompile(Tuple{getfield(Atom, Symbol("#283#285")),FuzzyCompletions.PropertyCompletion}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#39#40")) && precompile(Tuple{getfield(Atom, Symbol("#39#40"))}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#43#44")) && precompile(Tuple{getfield(Atom, Symbol("#43#44")),String}); catch err; @debug err; end
    try; isdefined(Atom, Symbol("#45#47")) && precompile(Tuple{getfield(Atom, Symbol("#45#47")),String}); catch err; @debug err; end
    try; @assert(let fbody = try __lookup_kwbody__(which(sprint, (Function,Atom.CompletionSuggestion,))) catch missing end
        if !ismissing(fbody)
            precompile(fbody, (Nothing,Int64,typeof(sprint),Function,Atom.CompletionSuggestion,))
        end
    end); catch err; @debug err; end
    try; @assert(precompile(Tuple{Core.kwftype(typeof(Atom.Type)),NamedTuple{(:rl, :ll, :url, :detail),NTuple{4,String}},Type{Atom.CompletionSuggestion},String,String,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Core.kwftype(typeof(Atom._collecttoplevelitems_static)),NamedTuple{(:inmod,),Tuple{Bool}},typeof(Atom._collecttoplevelitems_static),Nothing,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Core.kwftype(typeof(Atom.modulefiles)),NamedTuple{(:inmod,),Tuple{Bool}},typeof(modulefiles),String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Core.kwftype(typeof(Atom.toplevelitems)),NamedTuple{(:mod, :inmod),Tuple{String,Bool}},typeof(toplevelitems),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Atom.EvalError},StackOverflowError,Array{Base.StackTraces.StackFrame,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Atom.GotoItem},String,Atom.ToplevelCall})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Atom.GotoItem},String,Atom.ToplevelMacroCall})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Atom.GotoItem},String,Atom.ToplevelModuleUsage})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Axes,F,Args} where Args<:Tuple where F where Axes},typeof(Atom.localdatatip),Tuple{Array{Atom.ActualLocalBinding,1},Base.RefValue{SubString{String}},Int64}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{JSON.Writer.CompositeTypeWrapper},Atom.CompletionSuggestion,NTuple{9,Symbol}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{Type{Set},Array{OutlineItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.allprojects)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.appendline),String,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.DictCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.FieldCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.KeywordCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.ModuleCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.PathCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,FuzzyCompletions.PropertyCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,REPL.REPLCompletions.FieldCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,REPL.REPLCompletions.KeywordCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,REPL.REPLCompletions.ModuleCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,REPL.REPLCompletions.PathCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completion),Module,REPL.REPLCompletions.PropertyCompletion,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.completiondetail!),Dict{String,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.displayandrender),Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.displayandrender),Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.docs),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.eval),String,Int64,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.evalall),String,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.evalshow),String,Int64,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.evalsimple),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.finddevpackages)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.fullREPLpath),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.fuzzycompletionadapter),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.getmodule),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.handlemsg),Dict{String,Any},String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.handlemsg),Dict{String,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.isactive),Base.GenericIOBuffer{Array{UInt8,1}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.isanon),Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.localgotoitem),String,Nothing,Int64,Int64,Int64,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.md_hlines),MD})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.msg),String,Int64,Vararg{Any,N} where N})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.pkgpath),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.pluralize),Array{Int64,1},String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.processdoc!),MD,String,Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.processval!),Any,String,Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.processval!),Function,String,Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.project_info)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.project_status)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.realpath′),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Admonition})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.BlockQuote})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Code})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Footnote})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Header{1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Header{2}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.HorizontalRule})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.List})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMD),Markdown.Paragraph})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.Code})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.Footnote})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.Image})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.Italic})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.LaTeX})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),Markdown.Link})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.renderMDinline),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Nothing})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.render′),Juno.Inline,Type{T} where T})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.replcompletionadapter),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.rt_inf),Any,Method,Type})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.trim),Array{Float64,1},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.withpath),Function,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Any})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Array{String,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Array{Symbol,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Base.EnvDict})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Dict{Method,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Dict{String,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Dict{String,Array{String,1}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Dict{String,Dict{String,Array{Atom.GotoItem,1}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,ErrorException})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Float16})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Float32})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Float64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,OrderedCollections.OrderedDict{String,Union{NamedTuple{(:rt, :desc),Tuple{String,String}}, NamedTuple{(:f, :m, :tt),Tuple{Any,Method,Type}}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Regex})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,Type{T} where T})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsicon),Module,Symbol,UInt32})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wsitem),Module,Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,Any})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,ErrorException})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Atom.wstype),Module,Symbol,Type{T} where T})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.broadcasted),Function,Array{Atom.ActualLocalBinding,1},SubString{String},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.broadcasted),Function,Array{Atom.ActualLocalBinding,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.copyto_nonleaf!),Array{Dict{Symbol,Any},1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.localdatatip),Tuple{Base.Broadcast.Extruded{Array{Atom.ActualLocalBinding,1},Tuple{Bool},Tuple{Int64}},Base.RefValue{SubString{String}},Int64}},Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.copyto_nonleaf!),Array{Int64,1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.localdatatip),Tuple{Base.Broadcast.Extruded{Array{Atom.ActualLocalBinding,1},Tuple{Bool},Tuple{Int64}},Base.RefValue{SubString{String}},Int64}},Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.copyto_nonleaf!),Array{NamedTuple{(:name, :path),Tuple{String,String}},1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.project_info),Tuple{Base.Broadcast.Extruded{Array{String,1},Tuple{Bool},Tuple{Int64}}}},Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.copyto_nonleaf!),Array{Nothing,1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.outlineitem),Tuple{Base.Broadcast.Extruded{Array{Atom.ToplevelItem,1},Tuple{Bool},Tuple{Int64}}}},Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.copyto_nonleaf!),Array{OutlineItem,1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.outlineitem),Tuple{Base.Broadcast.Extruded{Array{Atom.ToplevelItem,1},Tuple{Bool},Tuple{Int64}}}},Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.materialize),Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Nothing,typeof(Atom.localdatatip),Tuple{Array{Atom.ActualLocalBinding,1},Base.RefValue{SubString{String}},Int64}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.Broadcast.restart_copyto_nonleaf!),Array{Union{Nothing, OutlineItem},1},Array{Nothing,1},Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.outlineitem),Tuple{Base.Broadcast.Extruded{Array{Atom.ToplevelItem,1},Tuple{Bool},Tuple{Int64}}}},OutlineItem,Int64,Base.OneTo{Int64},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base._promote_typejoin),Type{Nothing},Type{OutlineItem}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.allocatedinline),Type{Atom.GotoItem}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.allocatedinline),Type{Dict{String,Array{Atom.GotoItem,1}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to!),Array{Any,1},Base.Generator{Array{Any,1},typeof(Atom.renderMDinline)},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to!),Array{Hiccup.Node,1},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Dict{Symbol,Any},1},Dict{Symbol,Any},Base.Generator{Array{DocSeeker.DocObj,1},typeof(Atom.renderitem)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:a},1},Hiccup.Node{:a},Base.Generator{Array{Any,1},typeof(Atom.renderMDinline)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:code},1},Hiccup.Node{:code},Base.Generator{Array{Any,1},typeof(Atom.renderMDinline)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:div},1},Hiccup.Node{:div},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:h1},1},Hiccup.Node{:h1},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:h2},1},Hiccup.Node{:h2},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:hr},1},Hiccup.Node{:hr},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:img},1},Hiccup.Node{:img},Base.Generator{Array{Any,1},typeof(Atom.renderMDinline)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:pre},1},Hiccup.Node{:pre},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{Hiccup.Node{:p},1},Hiccup.Node{:p},Base.Generator{Array{Any,1},typeof(Atom.renderMD)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Base.collect_to_with_first!),Array{String,1},String,Base.Generator{Array{Any,1},typeof(Atom.renderMDinline)},Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Dict{Any,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Dict{Symbol,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:a}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:blockquote}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:em}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:h1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:h2}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:hr}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:img}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:li}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:pre}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:p}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:td}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:tr}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Hiccup.Node{:ul}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),Method})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Juno.view),SubString{String}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Atom.EvalError{StackOverflowError}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Hiccup.Node{:div}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Hiccup.Node{:span}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Juno.Model})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Text{String}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(Media.render),Juno.Inline,Type{T} where T})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(clearsymbols)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(convert),Type{Array{OutlineItem,1}},Array{Nothing,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(convert),Type{Array{OutlineItem,1}},Array{OutlineItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(convert),Type{Array{OutlineItem,1}},Array{Union{Nothing, OutlineItem},1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(convert),Type{Union{Nothing, Atom.Binding}},Atom.Binding})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(delete!),Dict{String,Dict{String,Array{Atom.GotoItem,1}}},String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(findfirst),Function,Array{Atom.CompletionSuggestion,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getdocs),Module,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Any,String,Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Any,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Any,Symbol,Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Any,Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Module,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Module,Symbol,Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getfield′),Module,Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getindex),Array{Atom.CompletionSuggestion,1},Array{Int64,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getindex),Dict{String,Array{Atom.GotoItem,1}},String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(getproperty),Atom.GotoItem,Symbol})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(globaldatatip),String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(globalgotoitems),String,Module,Nothing,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(globalgotoitems),String,Module,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(globalgotoitems_unloaded),String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(in),OutlineItem,Set{OutlineItem}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isempty),Array{Atom.GotoItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isempty),Array{Atom.ToplevelItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(ismacro),Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(ismacro),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Array{Any,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Array{String,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Array{Symbol,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Atom.Undefined})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Base.RefValue{Bool}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Base.RefValue{Tuple{String,Int64}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Dict{Method,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Dict{String,Any}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Dict{String,Array{String,1}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Dict{String,Dict{String,Array{Atom.GotoItem,1}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Function})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),HTML{String}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),OrderedCollections.OrderedDict{String,Union{NamedTuple{(:rt, :desc),Tuple{String,String}}, NamedTuple{(:f, :m, :tt),Tuple{Any,Method,Type}}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Regex})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(isundefined),Type{T} where T})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(length),Base.KeySet{String,Dict{String,Array{Atom.GotoItem,1}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(length),Base.KeySet{String,Dict{String,Dict{String,Array{Atom.GotoItem,1}}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(length),Dict{String,Array{Atom.GotoItem,1}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(map),Function,Array{Atom.CompletionSuggestion,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(map),Function,Array{Atom.GotoItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(map),Function,Array{OutlineItem,1}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(moduledefinition),Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(modulefiles),Module})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(modulefiles),String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(regeneratesymbols)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(searchcodeblocks),MD})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(searchdocs′),String,Bool,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(searchdocs′),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(setindex!),Array{OutlineItem,1},OutlineItem,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(similar),Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.localdatatip),Tuple{Base.Broadcast.Extruded{Array{Atom.ActualLocalBinding,1},Tuple{Bool},Tuple{Int64}},Base.RefValue{SubString{String}},Int64}},Type{Dict{Symbol,Any}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(similar),Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.outlineitem),Tuple{Base.Broadcast.Extruded{Array{Atom.ToplevelItem,1},Tuple{Bool},Tuple{Int64}}}},Type{Nothing}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(similar),Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.outlineitem),Tuple{Base.Broadcast.Extruded{Array{Atom.ToplevelItem,1},Tuple{Bool},Tuple{Int64}}}},Type{OutlineItem}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(similar),Base.Broadcast.Broadcasted{Base.Broadcast.DefaultArrayStyle{1},Tuple{Base.OneTo{Int64}},typeof(Atom.project_info),Tuple{Base.Broadcast.Extruded{Array{String,1},Tuple{Bool},Tuple{Int64}}}},Type{NamedTuple{(:name, :path),Tuple{String,String}}}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(sprint),Function,Base.Generator{CSTParser.EXPR,typeof(Atom.str_value)}})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(strlimit),String,Int64})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(toplevelitems),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(updatesymbols),String,Nothing,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(updatesymbols),String,String,String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(use_compiled_modules)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(vcat),OutlineItem,OutlineItem,OutlineItem,Vararg{OutlineItem,N} where N})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(workspace),String})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(|>),Array{Atom.CompletionSuggestion,1},typeof(length)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(|>),Array{Atom.GotoItem,1},typeof(isempty)})); catch err; @debug err; end
    try; @assert(precompile(Tuple{typeof(|>),Array{Atom.ToplevelItem,1},typeof(length)})); catch err; @debug err; end
end

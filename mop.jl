import TupleTools

abstract type Object end
struct IsObject <: Object end
struct IsNotObject <: Object end
Object(x) = IsNotObject()

macro defclass(form...)
    name = form[1]

    if length(form) >= 2
        supers = form[2]
    else
        supers = Expr(:tuple)
    end

    if length(form) >= 3
        slots = form[3]
    else
        slots = Expr(:tuple)
    end

    if isdefined(__module__, name)
        version = eval(Expr(:call, :classversion, name)) + 1
    else
        version = 1
    end

    ismutable = false

    structname = Symbol(name, "__v", version)
    structdeclaration = Expr(:struct, ismutable,
                            Expr(:(<:), structname, name),
                            Expr(:block, slots.args...))

    return quote
        abstract type $name end
        $structdeclaration
        global $name(y...) = $(Expr(:call, structname, Expr(:(...), esc(:y))))
        global superclasses(::Type{$name}) = isempty($supers) ? (Any,) : $supers
        global preclist(::Type{$name}) = expand_hierarchy($name)
        global Object(::Type{$name}) = IsObject()
        global classof(::$name) = $name

        global classversion(::Type{$name}) = $version

        @defmetaclass $name

        $name
    end
end

classversion(c) = 0

macro defmetaclass(name)
    return quote
        global classof(::Type{$name}) = StandardClass
        global superclasses(::Type{Type{$name}}) = (StandardClass,)
        global preclist(::Type{Type{$name}}) = expand_hierarchy(Type{$name})
        global Object(::Type{Type{$name}}) = IsObject()
    end
end

expand_hierarchy(::Tuple{}) = ()
function expand_hierarchy(type::Type)
    traversing = Set{Type}()
    traversed = Set{Type}()
    hierarchy = Vector{Type}()

    function topological(t::Type)
        if t in traversed
            return
        elseif t in traversing
            error("Circular class dependencies")
        end

        push!(traversing, t)

        for s in reverse(superclasses(t))
            topological(s)
        end

        pop!(traversing, t)
        push!(traversed, t)
        pushfirst!(hierarchy, t)
    end

    topological(type)
    return tuple(hierarchy...)
end

superclasses(x) = superclasses(Object(x), x)
superclasses(::IsObject, x) = error("Object with undefined superclasses")
superclasses(::IsNotObject, ::Type{Any}) = ()
superclasses(::IsNotObject, x) = (supertype(x),)

classof(x) = classof(Object(x), x)
classof(::IsObject, x) = error("Object with undefined classof")
classof(::IsNotObject, x) = typeof(x)
classof(::IsNotObject, ::Type) = StandardClass

preclist(x) = preclist(Object(x), x)
preclist(::IsObject, x) = error("Object with undefined preclist")
preclist(::IsNotObject, ::Type{Any}) = (Any,)
preclist(o::IsNotObject, x) = (x, preclist(o, supertype(x))...)

issubclass(a::Type, b::Type) = issubclass(Object(a), a, b)
function issubclass(::IsNotObject, a::Type, b::Type)
    a <: b
end
function issubclass(::IsObject, a::Type, b::Type)
    b in preclist(a)
end

Base.@pure compatibleargs(a::Tuple{}, b::Tuple{}) = true
Base.@pure compatibleargs(a::Tuple{}, b::Tuple) = false
Base.@pure compatibleargs(a::Tuple, b::Tuple{}) = false
Base.@pure function compatibleargs(a::Tuple, b::Tuple)
    if length(a) != length(b)
        false
    else
        for (i,j) in zip(a,b)
            if !issubclass(i,j)
                return false
            end
        end
        true
    end
end

args_more_specific(::Tuple{}, ::Tuple{}, ::Tuple{}) = error("Comparison of equal methods")
Base.@pure function args_more_specific(a::Tuple, b::Tuple, types::Tuple)
    if a[1] == b[1]
        args_more_specific(a[2:end], b[2:end], types[2:end])
    else
        precedences = preclist(types[1])
        idx1 = findtype(precedences, a[1])
        idx2 = findtype(precedences, b[1])
        return idx1 < idx2
    end
end

function findtype(x::Tuple, type::Type)
    for (k, v) in enumerate(x)
        if v == type
            return k
        end
    end
end
struct Fun
    lambda::Function
end

macro defmethod(form...)
    if length(form) == 1
        if (form[1].args[1].head == :call)
            name = form[1].args[1].args[1]
            combination = :primary
            args = form[1].args[1].args[2:end]
            body = form[1].args[2]
        elseif (form[1].args[1].head == :(::))
            name = form[1].args[1].args[1]
            combination = form[1].args[1].args[2].args[1]
            args = form[1].args[1].args[2].args[2:end]
            body = form[1].args[2]
        else
            error()
        end
    elseif length(form) == 2
        if (form[1].head == :call)
            name = form[1].args[1]
            combination = :primary
            args = form[1].args[2:end]
            body = form[2]
        elseif (form[1].head == :(::))
            name = form[1].args[1]
            combination = form[1].args[2].args[1]
            args = form[1].args[2].args[2:end]
            body = form[2]
        else
            error()
        end
    end
    
    types = get_types(args...)
    lenargs = length(args)
    generic_args = gen_generic_args(args...)
    generic_args_combination = Expr(generic_args.head, map(esc, generic_args.args)...,
                                    Expr(:(=), esc(:callnextmethod), esc(:nothing)),
                                    Expr(:(=), esc(:hasnextmethod), esc(:nothing)))
    defined = isdefined(__module__, name)

    lx = gensym(:x)

    return quote
        if $defined
            method_list = filter(gf_methods($(esc(name)))) do x
                x[1] != $types || x[3] != $(Expr(:quote, combination))
            end
        else
            method_list = ()
            global $name
            function $name end
        end

        global Base.@pure gf_methods(::typeof($name)) = (method_list..., ($types, Fun(@inline $generic_args_combination -> $(esc(body))), $(Expr(:quote, combination))))

        global $(gen_method(esc(name), generic_args, quote
            types = map(classof, $generic_args)
            methods = gf_methods($(esc(name)))
            compatible_methods = filter(x->compatibleargs(types, x[1]), methods)
            if length(compatible_methods) == 0
                error("No method found for ", $(esc(name)), " with args of types: ", types)
            end

            around_methods = filter(x->x[3] == :around, compatible_methods)
            around_methods = TupleTools.sort(around_methods, lt=(x,y) -> args_more_specific(x, y, types), by=x->x[1])

            before_methods = filter(x->x[3] == :before, compatible_methods)
            before_methods = TupleTools.sort(before_methods, lt=(x,y) -> args_more_specific(x, y, types), by=x->x[1])

            primary_methods = filter(x->x[3] == :primary, compatible_methods)
            primary_methods = TupleTools.sort(primary_methods, lt=(x,y) -> args_more_specific(x, y, types), by=x->x[1])

            after_methods = filter(x->x[3] == :after, compatible_methods)
            after_methods = TupleTools.sort(after_methods, lt=(x,y) -> args_more_specific(x, y, types), by=x->x[1], rev=true)

            around_methods_lambdas = map($lx -> $lx[2].lambda, around_methods)

            before_methods_lambdas = map($lx -> $lx[2].lambda, before_methods)

            primary_methods_lambdas = map($lx -> $lx[2].lambda, primary_methods)

            after_methods_lambdas = map($lx -> $lx[2].lambda, after_methods)

            lambdas = join_lambdas(around_methods_lambdas, before_methods_lambdas, after_methods_lambdas, primary_methods_lambdas)
            return lambdas($generic_args...)
        end))

        $(esc(name))
    end
end

@inline Base.@pure function join_lambdas(around::Tuple{}, before::Tuple{}, after::Tuple{}, primary::Tuple{})
    @inline (x...) -> nothing
end

@inline Base.@pure function join_lambdas(around::Tuple{}, before::Tuple{}, after::Tuple{}, primary::NTuple{1, Function})
    @inline (x...) -> begin
        callnextmethod(y...) = nonextmethod(y)
        hasnextmethod() = false
        primary[1](x..., callnextmethod, hasnextmethod)
    end
end

@inline Base.@pure function join_lambdas(around::Tuple{}, before::Tuple{}, after::Tuple{}, primary::Tuple)
    @inline (x...) -> begin
        next = join_lambdas(around, before, after, primary[2:end])
        callnextmethod() = next(x...)
        callnextmethod(y...) = next(y...)
        hasnextmethod() = true
        primary[1](x..., callnextmethod, hasnextmethod)
    end
end

@inline Base.@pure function join_lambdas(around::Tuple{}, before::Tuple{}, after::Tuple, primary::Tuple)
    @inline (x...) -> begin
        res = join_lambdas(around, before, after[1:end-1], primary)(x...)
        after[end](x...)
        return res
    end
end

@inline Base.@pure function join_lambdas(around::Tuple{}, before::Tuple, after::Tuple, primary::Tuple)
    @inline (x...) -> begin
        before[1](x...)
        join_lambdas(around, before[2:end], after, primary)(x...)
    end
end

@inline Base.@pure function join_lambdas(around::Tuple, before::Tuple, after::Tuple, primary::Tuple)
    @inline (x...) -> begin
        next = join_lambdas(around[2:end], before, after, primary)
        callnextmethod() = next(x...)
        callnextmethod(y...) = next(y...)
        hasnextmethod() = true
        around[1](x..., callnextmethod, hasnextmethod)
    end
end

extract_type(::Symbol) = :Any
extract_type(x::Expr) = (length(x.args) == 2 ? x.args[2]
                                             : x.args[1])

function get_types(args...)
    Expr(:tuple, map(extract_type, args)...)
end

get_types(::Symbol) = (Any,)

function gen_generic_args(args...)
    extract_symbol(x::Symbol) = x
    extract_symbol(x::Expr) = (length(x.args) == 2 ? x.args[1]
                                                   : gensym("var"))

    Expr(:tuple, map(extract_symbol, args)...)
end

gen_method(name, arg::Symbol, body::Expr) = gen_method(name,
            Expr(:tuple, arg), body)
gen_method(name, args::Expr, body::Expr) = Expr(:function, Expr(:call, name, args.args...),
    body)

@defclass StandardClass ()
@defclass StandardMethod ()

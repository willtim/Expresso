--
-- Expresso Prelude
--

type Maybe a = <Just : a, Nothing : {}>;
type Either a b = <Left : a, Right : b>;

let
    id    = x -> x;
    const = x y -> x;
    flip  = f x y -> (f y x);

    ----------------------------------------------------------------
    -- Basic list operations

    foldr       = f z -> fix (r xs ->
                           case uncons xs of
                             { Nothing{}         -> z
                             , Just {head, tail} -> f head (r tail)
                             });
    null        = xs -> case uncons xs of { Nothing{} -> True, Just{} -> False };
    map         = f -> foldr (x xs -> f x :: xs) [];
    filter      = f -> foldr (x xs -> if f x then (x::xs) else xs);
    length      = foldr (const (n -> 1 + n)) 0;
    foldl       = f z xs -> foldr (x xsf r -> xsf (f r x)) id xs z;
    concat      = xss -> foldr (xs ys -> xs ++ ys) [] xss;

    ----------------------------------------------------------------
    -- Maybe operations - smart constructors create closed variants

    just        : forall a. a -> Maybe a
                = x -> Just x;

    nothing     : forall a. Maybe a
                = Nothing{};

    maybe       : forall a b. b -> (a -> b) -> Maybe a -> b
                = b f m -> case m of { Just a -> f a, Nothing{} -> b };

    isJust      = maybe False (const True);
    isNothing   = maybe True (const False);
    fromMaybe   = x -> maybe x id;
    listToMaybe = foldr (x -> const (just x)) nothing;
    maybeToList = maybe [] (x -> [x]);
    catMaybes   = xs -> concat (map maybeToList xs);
    mapMaybe    = f -> maybe nothing (just << f);

    ----------------------------------------------------------------
    -- Either operations - smart constructors create closed variants

    left        : forall a b. a -> Either a b
                = x -> Left x;

    right       : forall a b. b -> Either a b
                = x -> Right x;

    either      : forall a b c. (a -> c) -> (b -> c) -> Either a b -> c
                = f g m -> case m of { Left a -> f a, Right b -> g b };

    ----------------------------------------------------------------
    -- Logical operations

    and =  foldr (x y -> x && y) True;
    or  =  foldr (x y -> x || y) False;
    any =  p -> or << map p;
    all =  p -> and << map p;

    elem    = x -> any (x' -> x' == x);
    notElem = x -> all (x' -> x' /= x);

    ----------------------------------------------------------------
    -- Dynamic binding

    withOverride  = overrides f self -> overrides (f self);
    mkOverridable = f -> { override_ = overrides -> (withOverride overrides f) | fix f};

    override = r overrides -> mkOverridable (r.override_ overrides)


-- Exports
in { id
   , const
   , foldr
   , null
   , map
   , filter
   , length
   , foldl
   , concat
   , just
   , nothing
   , maybe
   , isJust
   , isNothing
   , fromMaybe
   , listToMaybe
   , maybeToList
   , catMaybes
   , mapMaybe
   , left
   , right
   , either
   , and
   , or
   , any
   , all
   , elem
   , notElem
   , mkOverridable
   , override
   }

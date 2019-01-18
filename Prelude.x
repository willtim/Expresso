--
-- Expresso Prelude
--
let

    id    = x -> x;
    const = x y -> x;
    flip  = f x y -> (f y x);

    ----------------------------------------------------------------
    -- List operations

    map         = f -> foldr (x xs -> f x :: xs) [];
    filter      = f -> foldr (x xs -> if f x then (x::xs) else xs);
    length      = foldr (const (n -> 1 + n)) 0;
    foldl       = f z xs -> foldr (x xsf r -> xsf (f r x)) id xs z;
    reverse     = foldl (xs x -> x :: xs) [];
    concat      = xss -> foldr (xs ys -> xs ++ ys) [] xss;
    intersperse = sep xs ->
        let f   = x xs -> (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;
    intercalate = xs xss -> concat (intersperse xs xss);

    ----------------------------------------------------------------
    -- Maybe operations - smart constructors create closed variants

    just        : forall a. a -> <Just : a, Nothing : {}>
                = x -> Just x;

    nothing     : forall a. <Just : a, Nothing : {}>
                = Nothing{};

    maybe       : forall a b. b -> (a -> b) -> <Just : a, Nothing : {}> -> b
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

    left        : forall a b. a -> <Left : a, Right : b>
                = x -> Left x;

    right       : forall a b. b -> <Left : a, Right : b>
                = x -> Right x;

    either      : forall a b c. (a -> c) -> (b -> c) -> <Left : a, Right : b> -> c
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
   , map
   , filter
   , length
   , foldl
   , reverse
   , concat
   , intercalate
   , intersperse
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

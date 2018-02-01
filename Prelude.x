--
-- Expresso Prelude
--
let

    id    = x -> x;
    const = x y -> x;
    flip  = f x y -> (f y x);

    ------------------------------------------------------------
    -- List operations

    map         = f -> foldr (x xs -> f x :: xs) [];
    filter      = f -> foldr (x xs -> if f x then (x::xs) else xs);
    length      = foldr (const (n -> 1 + n)) 0;
    foldl       = f z xs -> foldr (x xsf r -> xsf (f r x)) id xs z : forall b a. (b -> a -> b) -> b -> [a] -> b;
    reverse     = foldl (xs x -> x :: xs) [];
    concat      = xss -> foldr (xs ys -> xs ++ ys) [] xss;
    intersperse = sep xs ->
        let f   = x xs -> (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;
    intercalate = xs xss -> concat (intersperse xs xss);
    lookup = m xs -> case foldl (state elem -> case state of {LookingAt n -> if (n == m) then Found elem else (LookingAt (n + 1)), Found x -> Found x}) (LookingAt 0) xs of { Found x -> Found x, LookingAt n -> NotFound{} } : (forall a. Int -> [a] -> <Found : a, NotFound : {}>);

    ------------------------------------------------------------
    -- Maybe operations

    maybe       = (z f mb -> case mb of { Nothing {} -> z, Just x -> f x })
                : forall a b r. b -> (a -> b) -> <Nothing : {}, Just : a> -> b;
    isJust      = maybe False (const True);
    isNothing   = maybe True (const False);
    fromMaybe   = x -> maybe x id;
    listToMaybe = foldr (x -> const (Just x)) (Nothing {});
    maybeToList = maybe [] (x -> [x]);
    catMaybes   = xs -> concat (map maybeToList xs);
    mapMaybe    = f -> maybe (Nothing {}) (Just << f);

    ------------------------------------------------------------
    -- Logical operations

    and =  foldr (x y -> x && y) True;
    or  =  foldr (x y -> x || y) False;
    any =  p -> or << map p;
    all =  p -> and << map p;

    elem    = x -> any (x' -> x' == x);
    notElem = x -> all (x' -> x' /= x);

    ------------------------------------------------------------
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
   , maybe
   , isJust
   , isNothing
   , fromMaybe
   , listToMaybe
   , maybeToList
   , catMaybes
   , mapMaybe
   , and
   , or
   , any
   , all
   , elem
   , notElem
   , mkOverridable
   , override
   , lookup
   }

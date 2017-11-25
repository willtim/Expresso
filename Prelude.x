--
-- Expresso Prelude
--
let

    id = x: x;
    const = x: y: x;

    ------------------------------------------------------------
    -- List operations

    map = f: foldr (x: xs: f x :: xs) [];
    filter = f: foldr (x: xs: if f x then (x::xs) else xs);
    length = foldr (const (n: 1 + n));
    foldl = f: z: xs: foldr (x: xsf: r: xsf (f r x)) id xs z;
    reverse = foldl (xs: x: x :: xs) [];
    concat = xss: foldr (xs: ys: xs ++ ys) [] xss;
    intersperse = sep: xs:
        let f = x: xs: (if null xs then [x] else x :: sep :: xs)
        in foldr f [] xs;
    intercalate = xs: xss: concat (intersperse xs xss);

    ------------------------------------------------------------
    -- Maybe operations

    isJust = maybe False (const True);
    isNothing = maybe True (const False);
    fromMaybe = x: maybe x id;
    listToMaybe = foldr (x: const (Just x)) Nothing;
    maybeToList = maybe [] (x: [x]);
    catMaybes = xs: concat (map maybeToList xs);
    mapMaybe = f: maybe Nothing (Just << f);

    ------------------------------------------------------------
    -- Dynamic binding

    withOverride = overrides: f: self: overrides (f self);
    mkOverridable = f: { override_ = overrides: (withOverride overrides f) | fix f};

    -- our exported override function
    override = r: overrides: mkOverridable (r.override_ overrides)


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
   , isJust
   , isNothing
   , fromMaybe
   , listToMaybe
   , maybeToList
   , catMaybes
   , mapMaybe
   , mkOverridable
   , override
   }

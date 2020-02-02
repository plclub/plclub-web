{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
 - Module: PLClub.HakyllExtra
 - Description: Extra general-purpose Hakyll features
 -}

module PLClub.HakyllExtra where
--------------------------------------------------------------------------------

import       Hakyll
import       System.FilePath.Posix
import       Data.List (reverse)
import       Control.Monad (liftM)
import       Data.Ord (comparing)
import       Data.List (sortBy)

--- Suppose
-- C is a compiler that returns a LIST (x) of LISTS (y)
-- I want a context D that will execute against the first list (x)
-- It will a take a key ("group") and a context E to run on an inner lists y.
-- Then it is a totally different Context b. When executed in runs C to get [[a]].
-- Against each list [a] it runs E.
-- Meanwhile E is running against a "Compiler [a]". E should be use a listFieldWith
-- because it is executing NOT against a STORED set (the 3rd argument to listField).
-- No, it must generated the set.
-- And it will run C to get [[a]]. For each

nestedListField :: String -- outer key
      -> String -- inner key
      -> Context a
      -> Compiler [[Item a]]
      -> Context b
nestedListField ko ki ctx items =
    listField ko innerctx ((Item "" <$>) <$> items)
  where
    innerctx = listFieldWith ki ctx (\(Item _ as) -> return as)
 
defaultContextDate :: Context String
defaultContextDate =
    dateField "date" "%b %e %Y" `mappend`
    defaultContext


-- Load a list of items whose tag field matches some key
-- Note that `rulesExtraDependencies` is required to register
-- dependency on the `Tags`
loadTag :: Tags -- ^ Tags structure
        -> String -- ^ Key
        -> Compiler [Item String]
loadTag tags tag = do
    loadAll (fromList identifiers)
  where
    identifiers = maybe [] id $ lookup tag (tagsMap tags)


-- | Rename `myfile.ext` to `myfile/index.ext` This is prettier and
-- good for SEO, since we can simply use `domain.tld/myfile/` vs.
-- `domain.tld/myfile.ext`
canonizeRoute :: Routes
canonizeRoute =
    customRoute $ \ident ->
        let fn = toFilePath ident
        in  takeDirectory fn </>
                takeBaseName fn  </>
                "index" -<.>
                (takeExtension fn)

-- | Drop redundant `/index.html` from a URL, if necessary
canonizeUrl :: String -> String
canonizeUrl url = canon
  where
    l = length ("index.html" :: String)
    canon =
        if "/index.html" == (reverse . take (l+1) . reverse $ url)
            then reverse $ drop l (reverse url)
            else url
 
         
getCanonicalRoute :: Identifier -> Compiler (Maybe FilePath)
getCanonicalRoute item = do
        mroute <- getRoute item
        return (canonizeUrl <$> mroute)

-- | Canonize URLs.
-- It is unfortunate to have to copy+paste Hakyll's code here,
-- but there's no way to map `canonizeURL` over a `Context a`
canonicalUrlField :: String -> Context String
canonicalUrlField key = field key $ \i -> do
    let id = itemIdentifier i
        empty' = fail $ "No route url found for item " ++ show id
    fmap (maybe empty' toUrl) $ getCanonicalRoute id

-- | Global context
-- Note that an item's title will either be set explicitly in its metadata
-- or based on its filename (dropping up to the first '-')
siteContext :: Context String
siteContext =
    metadataField      `mappend`
    dateField  "date" "%b %e %Y" `mappend`
    bodyField  "body"  `mappend`
    titleField "title" `mappend`
    canonicalUrlField   "url" `mappend`
    missingField
    
-- | Get graduation year field
-- Look up the "year" field of an identifier's metadata
-- Will throw a runtime error if the field does not exist
-- or cannot be coerced to an integer
getYear :: (MonadMetadata m)
        => Item a
        -> m Int
getYear item =
  read <$> getMetadataField' (itemIdentifier item) "year"

sortByM :: (Monad m, Ord k) => (a -> m k) -> [a] -> m [a]
sortByM f xs = liftM (map fst . sortBy (comparing snd)) $
  mapM (\x -> liftM (x,) (f x)) xs

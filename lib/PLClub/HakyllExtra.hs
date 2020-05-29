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
import       Control.Monad.Fail (MonadFail)
import       Data.Ord (comparing)
import       Data.List (sortBy)
import       PLClub.PandocExtra (makeTOC)

-- | Create a 'listField' whose inner 'Context' is another
-- @listField@.
--
-- @nestedListField ko ki ctx items@ is a list
-- with key @ko@. The values of that list are the outer elements of
-- type @[Item a]@. Those elements are seen in a context in which
-- there is a single inner context with key @ki@ and whose values are
-- the individual @Item a@ values rendered in the original context.
nestedListField :: String -- outer key
                -> String -- inner key
                -> Context a
                -> Compiler [[Item a]]
                -> Context b
nestedListField ko ki ctx items =
    listField ko innerctx ((Item "" <$>) <$> items)
  where
    innerctx = listFieldWith ki ctx (\(Item _ as) -> return as)

-- | Load a list of items whose tag field matches some key
--
-- Note that `rulesExtraDependencies` is required to register
-- dependency on the `Tags`
loadTag :: Tags -- ^ Tags structure
        -> String -- ^ Key
        -> Compiler [Item String]
loadTag tags tag = do
    loadAll (fromList identifiers)
  where
    identifiers = maybe [] id $ lookup tag (tagsMap tags)

-- | Make a dedicated folder for the compiled 'Item'. E.g.:
--
--    * @\/foo.ext@ becomes @\/foo\/index.ext@
--    * @\/foo\/bar.ext@ becomes @\/foo\/bar\/index.ext@
--
-- The resulting URLs are prettier and more user-friendly when paired
-- with 'canonicalUrlField'
makeIntoFolder :: Routes
makeIntoFolder = customRoute $ \ident ->
    let fn = toFilePath ident
    in takeDirectory fn </>
       takeBaseName fn  </>
       "index" -<.>
       takeExtension fn

-- | Type of a blog post file
data Blogfile =
    Blogpost
  | Blogartifact
  deriving (Eq)

-- | Determine the type of a blog post file
getBlogType :: Identifier -> Blogfile
getBlogType ident =
  let path = splitDirectories (toFilePath ident)
  in case path of
       "blog" : file : [] -> Blogpost
       "blog" : folder : something : rest ->
         if takeBaseName something == folder
         then Blogpost
         else Blogartifact
       _ -> error "getBlogType: I don't know what to do with this file"

-- | A smart function to route blog posts into their own folders, if necessary.
--
-- If a blog post is stored in its own folder, the folder name should
-- be dated. Then the unique file whose name begins with the __same__
-- date is used as the @index.html@ file. If instead there is a
-- filename of @index.ext@, that is the index file. Other files and
-- nested folders are routed with their same names and structure, to be linked to
-- within the blog post.
--
--    * @\/blog\/date-title.ext@ becomes @\/blog\/date-title\/index.ext@
--    * @\/blog\/date-title\/index.ext@ becomes @\/blog\/date-title\/index.ext@
--    * @\/blog\/date-title\/date-title2.ext@ becomes @\/blog\/date-title2\/index.ext@
--    * @\/blog\/date-title\/artifact.ext@ becomes @\/blog\/date-title\/artifact.ext@
blogPostRoute :: Routes
blogPostRoute = customRoute $ \ident ->
  case getBlogType ident of
    Blogpost -> "blog" </> takeBaseName (toFilePath ident) </> "index.html"
    Blogartifact -> toFilePath ident

-- | Load only blog posts (no artifacts) from the @blog/@ directory
loadAllBlogPosts :: Compiler [Item String]
loadAllBlogPosts = do
  items <- loadAll ("blog/*/*" .||. "blog/*")
  return (filter itemIsPost items)
    where
      itemIsPost :: Item a -> Bool
      itemIsPost item =
        getBlogType (itemIdentifier item) == Blogpost

-- | Drop redundant `/index.html` from a URL 'String', if present
--
-- We call the result the _canonical_ url.
canonizeUrlString :: String
                  -> String
canonizeUrlString url = canon
  where
    len = length ("index.html" :: String)
    inreverse op list = reverse (op (reverse list))
    canon =
        if "/index.html" == inreverse (take (len + 1)) url
        then inreverse (drop len) url
        else url

-- | A field to obtain the prettified (canonical) URL for an 'Item'
--
-- This field is use, for example, when generating links to blog posts.
canonicalUrlField :: String -> Context String
canonicalUrlField key = field key $ \item -> do
    let ident = itemIdentifier item
        empty' = fail $ "No route found for item " ++ show ident
    mroute <- getRoute ident
    case mroute of
      Nothing -> empty'
      Just r -> return $ toUrl (canonizeUrlString r)

-- | A "table of contents" field
tocField :: String -- ^ The name for the created field
         -> Context String
tocField key = field key $ \_ -> do
  itemtoc <- makeTOC
  let toc = itemBody itemtoc
  return toc

-- | Default context for rendering most templates.
siteContext :: Context String
siteContext = mconcat $
    [ metadataField
    , dateField  "date" "%b %e %Y"
    , bodyField  "body"
    , titleField "title"
    , canonicalUrlField "url"
    , tocField "toc"
    , missingField
    ]

-- | Lookup graduation year field of an 'Item'
--
-- Look up the "year" field of an identifier's metadata Will throw a
-- runtime error if the field does not exist or cannot be coerced to
-- an integer. Throws a runtime error if this field does not exist.
getYear :: (MonadMetadata m, MonadFail m)
        => Item a -- ^ The item whose @year@ field to lookup
        -> m Int  -- ^ The year as an 'Int'
getYear item =
  read <$> getMetadataField' (itemIdentifier item) "year"

-- | A monadic version of 'Data.List.sortOn'
--
-- Given a monadic computation for computing a key, and a list of values,
-- sort the list of values within the monad.
sortOnM :: (Monad m, Ord k) => (a -> m k) -> [a] -> m [a]
sortOnM f xs = liftM (map fst . sortBy (comparing snd)) $
  mapM (\x -> liftM (x,) (f x)) xs

-- | Drop the top-most folder of a filepath. For example:
--
--     * @\/foo\/bang.ext@ becomes @\/bang.ext@
--     * @\/foo\/bar\/bang.ext@ becomes @\/bar\/bang.ext@
--     * @\/bang.ext@ generates a runtime error
routeTail :: Routes
routeTail = customRoute $ \ident ->
  let path = splitDirectories (toFilePath ident)
  in if length path <= 1
     then error "[routeTail] expects a path with a leading folder to drop"
     else joinPath (tail path)

-- | Drop the entire folder structure and dump into a flat folder
-- named by the argument. For example, @flattenIntoFolder "foo"@:
--
--     * Routes @\/bang.ext@ to @\/foo\/bang.ext@
--     * Routes @\/bar\/bang.ext@ to @\/foo\/bang.ext@
--     * Routes @\/bar\/baz\/bang.ext@ to @\/foo\/bang.ext@
flattenIntoFolder :: String -- ^ The folder to output into
                  -> Routes
flattenIntoFolder folder = customRoute $ \ident ->
  folder </> takeFileName (toFilePath ident)

-- | A hackish filder to output a hidden @htaccess@ file
--
-- There is a folder from the old site which contains an Apache
-- @htaccess@ file which must be named with a leading @'.'@.  This
-- file is stored un-hidden within the repo, then renamed
-- appropriately by this filter.
htaccessHackRoute :: Routes
htaccessHackRoute = customRoute $
    hack . toFilePath
  where
    hack path =
      if takeBaseName path == "htaccess"
      then replaceBaseName path ".htaccess"
      else path

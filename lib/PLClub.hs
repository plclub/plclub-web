{-# LANGUAGE OverloadedStrings #-}
{-|
 - Module: PLClub
 - Description: Top-level module for PLClub website
 -}

module PLClub where

--------------------------------------------------------------------------------
import           Data.Monoid (mappend)
import           Hakyll
import           PLClub.Publications 

--------------------------------------------------------------------------------
application :: IO ()
application = hakyll $ do
    match "img/**" $ do
        route   idRoute
        compile copyFileCompiler

    match "vendor/**" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

    match "people/*" $ do
        compile getResourceBody

    match "meetings/*" $ do
        route $ setExtension "html"
        compile $ do
            pandocCompiler
                >>= loadAndApplyTemplate "templates/meeting.html" defaultContextDate 
                >>= loadAndApplyTemplate "templates/default.html"  defaultContext
                >>= relativizeUrls

    --people tags
    ptags <- buildTags "people/*" (fromCapture "ptags/*.html")
    
        
    create ["people.html"] $ rulesExtraDependencies [tagsDependency ptags] $ do
        route idRoute
        compile $ do
            let faculty = (unbindList 4) <$> loadTag ptags "faculty" :: Compiler [[Item String]]
            let students = (unbindList 4) <$> loadTag ptags "student" :: Compiler [[Item String]]
            let peopleGroupCtx = 
                    magic faculty "facultyGroup" "faculty" defaultContext `mappend`
                    magic students "studentGroup" "students" defaultContext `mappend`
                    constField "title" "People"            `mappend`
                    defaultContext
            makeItem ""
                >>= loadAndApplyTemplate "templates/people.html" peopleGroupCtx
                >>= loadAndApplyTemplate "templates/default.html" defaultContext 
                >>= relativizeUrls

    create ["papers.html"] $ do
        route idRoute
        compile $ do
            let ctx =
                    papersContext
                    `mappend` defaultContext
            getResourceBody
                >>= applyAsTemplate ctx 
                >>= loadAndApplyTemplate "templates/default.html" defaultContext 
                >>= relativizeUrls

    match "club.html" $ do
        route idRoute
        compile $ do
            meetings <- recentFirst =<< loadAll "meetings/*"
            let meetingsCtx =
                    listField "meetings" defaultContextDate (return meetings) `mappend`
                    constField "title" "Penn PL Club" `mappend`
                    defaultContext
            getResourceBody
                >>= applyAsTemplate meetingsCtx
                >>= loadAndApplyTemplate "templates/default.html" meetingsCtx
                >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            meetings <- recentFirst =<< loadAll "meetings/*"
            let indexCtx =
                    listField "meetings" defaultContextDate (return meetings) `mappend`
                    recentPapersContext `mappend`
                    constField "title" "Home"                `mappend`
                    defaultContext
            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------
defaultContextDate :: Context String
defaultContextDate =
    dateField "date" "%B %e, %Y" `mappend`
    defaultContext


unbindList :: Int -> [a] -> [[a]]
unbindList _ [] = []
unbindList n as =
    (take n as):(unbindList n $ drop n as)

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

magic :: Compiler [[Item a]]
      -> String -- outer key
      -> String -- inner key
      -> Context a
      -> Context b
magic comp ko ki ctx =
    listField ko innerctx ((Item "" <$>) <$> comp)
  where
    innerctx = listFieldWith ki ctx (\(Item _ as) -> return as)

loadTag :: Tags -> String -> Compiler [Item String]
loadTag tags tag = do
    loadAll (fromList identifiers)
  where
    identifiers = maybe [] id $ lookup tag (tagsMap tags)

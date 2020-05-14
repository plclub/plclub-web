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
import           PLClub.HakyllExtra

-- | Compose routes, renamed to emphasize
-- that LHS is applied before RHS
(<!>) = composeRoutes
thenRoute = composeRoutes

config :: Configuration
config = defaultConfiguration
  { deployCommand = "./extra/deploy.sh"
  }
  
--------------------------------------------------------------------------------
application :: IO ()
application = hakyllWith config $ do
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
        route   $ idRoute <!> setExtension "html" <!> canonizeRoute
        compile $ do
            pandocCompiler
                >>= loadAndApplyTemplate "templates/meeting.html" siteContext 
                >>= loadAndApplyTemplate "templates/default.html"  siteContext
                >>= relativizeUrls

    --people tags
    ptags <- buildTags "people/*" (fromCapture "ptags/*.html")

    create ["papers.html"] $ do
        route   $ idRoute <!> canonizeRoute
        compile $ do
            let ctx =
                    papersContext
                    `mappend` siteContext
            getResourceBody
                >>= applyAsTemplate ctx 
                >>= loadAndApplyTemplate "templates/default.html" siteContext 
                >>= relativizeUrls

    create ["papers/plclub_bib.html"] $ do
        route   $ idRoute
        compile $ do
            makeItem =<< unsafeCompiler makeBibHtml

    match "club.html" $ do
        route   $ idRoute <!> canonizeRoute
        compile $ do
            meetings <- recentFirst =<< loadAll "meetings/*"
            let meetingsCtx =
                    listField "meetings" siteContext (return meetings) `mappend`
                    constField "title" "Penn PL Club" `mappend`
                    siteContext
            getResourceBody
                >>= applyAsTemplate meetingsCtx
                >>= loadAndApplyTemplate "templates/default.html" meetingsCtx
                >>= relativizeUrls

    match "old_site/**" $ do
      route   $ routeTail <!> htaccessHackRoute
      compile $ copyFileCompiler
        
        

    match "index.html" $ do
        rulesExtraDependencies [tagsDependency ptags] $ do
            route idRoute
            compile $ do
                meetings <- recentFirst =<< loadAll "meetings/*"
                let indexCtx =
                        peopleContext ptags `mappend`
                        listField "meetings" siteContext (return meetings) `mappend`
                        recentPapersContext `mappend`
                        constField "title" "Home"                `mappend`
                        siteContext
                getResourceBody
                    >>= applyAsTemplate indexCtx
                    >>= loadAndApplyTemplate "templates/default.html" indexCtx
                    >>= relativizeUrls

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------
unbindList :: Int -> [a] -> [[a]]
unbindList _ [] = []
unbindList n as =
    (take n as):(unbindList n $ drop n as)

peopleContext :: Tags -> Context String
peopleContext ptags = 
  let faculty  = (unbindList 3) <$> loadTag ptags "faculty" :: Compiler [[Item String]]
      students = (unbindList 3) <$> loadTag ptags "student" :: Compiler [[Item String]]
      postdocs = (unbindList 3) <$> loadTag ptags "postdoc" :: Compiler [[Item String]]
      alum'    = loadTag ptags "alum" :: Compiler [Item String]
      alum     = reverse <$> (sortByM getYear =<< alum')
  in
    nestedListField "facultyGroup" "faculty" siteContext faculty `mappend`
    nestedListField "studentGroup" "student" siteContext students`mappend`
    nestedListField "postdocGroup" "postdoc" siteContext postdocs`mappend`
    listField "alum" siteContext alum

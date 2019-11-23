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
        route   $ idRoute <!> setExtension "html" <!> canonizeRoute
        compile $ do
            pandocCompiler
                >>= loadAndApplyTemplate "templates/meeting.html" siteContext 
                >>= loadAndApplyTemplate "templates/default.html"  siteContext
                >>= relativizeUrls

    --people tags
    ptags <- buildTags "people/*" (fromCapture "ptags/*.html")
    
        
    create ["people.html"] $ rulesExtraDependencies [tagsDependency ptags] $ do
        route   $ idRoute <!> canonizeRoute
        compile $ do
            let faculty = (unbindList 4) <$> loadTag ptags "faculty" :: Compiler [[Item String]]
            let students = (unbindList 4) <$> loadTag ptags "student" :: Compiler [[Item String]]
            let peopleGroupCtx = 
                    nestedListField "facultyGroup" "faculty" siteContext faculty `mappend`
                    nestedListField "studentGroup" "students" siteContext students`mappend`
                    constField "title" "People"            `mappend`
                    siteContext
            makeItem ""
                >>= loadAndApplyTemplate "templates/people.html" peopleGroupCtx
                >>= loadAndApplyTemplate "templates/default.html" siteContext 
                >>= relativizeUrls

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

    create ["plclub_bib.html"] $ do
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

    match "index.html" $ do
        route idRoute
        compile $ do
            meetings <- recentFirst =<< loadAll "meetings/*"
            let indexCtx =
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

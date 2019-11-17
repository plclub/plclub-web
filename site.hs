--------------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
import           Data.Monoid (mappend)
import           Hakyll
import		 System.IO.Temp (withSystemTempDirectory)
import		 System.Directory (copyFile)
import		 System.FilePath.Posix ((</>))
import		 System.Process (callProcess)
import		 Text.Pandoc.Definition
import		 Text.Pandoc (writeHtml5String, readHtml)
import		 Text.Pandoc.Class (runPure)
import		 Data.Text (unpack, pack)


--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
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
		saveSnapshot "content" =<< getResourceBody
		pandocCompiler
                >>= loadAndApplyTemplate "templates/meeting.html" defaultContextDate 
                >>= loadAndApplyTemplate "templates/default.html"  defaultContext
            	>>= relativizeUrls

    create ["people.html"] $ do
        route idRoute
        compile $ do
            people <- loadAll "people/*" :: Compiler [Item String]
            people4 <- (\is -> Item "" <$> unbindList 4 is) <$> loadAll "people/*" :: Compiler [Item [Item String]]
            let peopleGroupCtx =
                    listField "peopleGroup" peopleCtx (return people4) `mappend`
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
                    papersContext                `mappend`
                    defaultContext
            getResourceBody
                >>= applyAsTemplate ctx 
                >>= loadAndApplyTemplate "templates/default.html" defaultContext 
                >>= relativizeUrls

		{-
    create ["papers.html"] $ do
    	route idRoute
    	compile $ do
		str <- unsafeCompiler $ do
			withSystemTempDirectory "plclub_bib" $ \f -> do
				return $ "pl club html contents" ++ (show f) :: IO String
				copyFile "papers/Makefile" (f </> "Makefile")
				copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
				callProcess "make" ["-C", f]
				readFile (f </> "plclub.html")
		pan <- makeItem str
		pan' <- readPandoc pan :: Compiler (Item Pandoc)
		return pan'
		--return (writePandoc (getRows 5 <$> pan'))
			-- >>= loadAndApplyTemplate "templates/papers.html" defaultContext
			-- >>= loadAndApplyTemplate "templates/default.html" defaultContext
			-- >>= relativizeUrls
	-}

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

getRows :: Int -> Pandoc -> Pandoc
getRows n (Pandoc m blocks) =
	Pandoc m $ go <$> blocks
  where
  	go (Table i a d c rows) =
		Table i a d c (take n rows)
	go x = x

justRows :: Int -> Pandoc -> [Pandoc] 
justRows n (Pandoc m blocks) =
	splitTable table
  where
  	table = head $ dropWhile (not . isTable) blocks
  	isTable (Table _ _ _ _ _) = True 
	isTable _ = False 
	splitTable (Table i a d c rows) = 
		(Pandoc m . secondCell) <$> rows
	{-
	findtable x = case x of
		| Table i a d c rows -> 
		| Plain _ = error "Found a plain" 
		| Para _ = error "Found a Para" 
		| LineBlock _ = error "Found a LineBlock" 
		| CodeBlock _ _ = error "Found a CodeBlock"
		|

	-}
	secondCell (_:x:_) = x


getPapers :: Compiler [String]
getPapers = do
	unsafeCompiler $ do
		withSystemTempDirectory "plclub_bib" $ \f -> do
			return $ "pl club html contents" ++ (show f) :: IO String
			copyFile "papers/Makefile" (f </> "Makefile")
			copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
			callProcess "make" ["-C", f]
			str <- readFile (f </> "plclub.html")
			return $ case runPure $ readHtml defaultHakyllReaderOptions (pack str) of
				Left err -> error "Shit"
				Right pan -> do
					let pans = justRows 5 pan
					flip map pans $ \p -> do
						case runPure $ (writeHtml5String defaultHakyllWriterOptions) p of
							Left err -> error "Writing shit"
							Right txt -> unpack txt


getPapersItems :: Compiler [Item String]
getPapersItems = do
	strs <- getPapers
	return $ Item "" <$> strs

getRecentPapers :: Compiler [Item String]
getRecentPapers = do
	strs <- take 5 <$> getPapers
	return $ Item "" <$> strs

papersContext :: Context a
papersContext = listField "papers" defaultContext getPapersItems
	
recentPapersContext :: Context a
recentPapersContext = listField "recentpapers" defaultContext getRecentPapers

{-
peopleListCtx :: Context [Item String]
peopleListCtx =
	listField "persongroup"

peopleListList :: Context [Item [Item String]]
peopleListList =
	listField "persongroup"
	-}

unbindList :: Int -> [a] -> [[a]]
unbindList _ [] = []
unbindList n as =
	(take n as):(unbindList n $ drop n as)


peopleCtx :: Context [Item String]
peopleCtx = listFieldWith "people" defaultContext (\(Item _ v) -> return v)

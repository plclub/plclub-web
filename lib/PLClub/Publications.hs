{-# LANGUAGE OverloadedStrings #-}

{-|
 - Module: PLClub.Publications
 - Description: Support for assembling publications
 -}

module PLClub.Publications where
--------------------------------------------------------------------------------

import       Data.Monoid (mappend)
import       Hakyll
import       System.IO.Temp (withSystemTempDirectory)
import       System.Directory (copyFile)
import       System.FilePath.Posix ((</>))
import       System.Process (callProcess)
import       Text.Pandoc.Definition
import       Text.Pandoc (writeHtml5String, readHtml)
import       Text.Pandoc.Class (runPure)
import       Data.Text (unpack, pack)



-- | A compiler action that assembles the webpage in a temporary directory,
-- parses everything, and returns a list of strings
compilePapers :: Compiler [String]
compilePapers = do
    unsafeCompiler $ do
        html <- makePapersHtml
        return $ parsePapers html


-- Assemble "plclub.html" as a String
-- This part purely runs the Makefile and returns "plclub.html"
-- No Hakyll stuff happening yet
makePapersHtml :: IO String
makePapersHtml = withSystemTempDirectory "plclub_bib" $ \f -> do
    copyFile "papers/Makefile" (f </> "Makefile")
    copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
    callProcess "make" ["-C", f]
    readFile (f </> "plclub.html")

-- Assemble "plclub_bib.html" as a String
-- This part purely runs the Makefile and returns "plclub.html"
-- No Hakyll stuff happening yet
makeBibHtml :: IO String
makeBibHtml = withSystemTempDirectory "plclub_bib" $ \f -> do
    copyFile "papers/Makefile" (f </> "Makefile")
    copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
    callProcess "make" ["-C", f]
    readFile (f </> "plclub_bib.html")

-- Assemble "merged.bib" as a String
makeMergedBib :: IO String
makeMergedBib = withSystemTempDirectory "plclub_bib" $ \f -> do
    copyFile "papers/Makefile" (f </> "Makefile")
    copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
    callProcess "make" ["-C", f, "merged.bib"]
    readFile (f </> "merged.bib")

-- This uses pandoc to parse the papers
parsePapers :: String -> [String]
parsePapers src = 
    case runPure $ readHtml defaultHakyllReaderOptions (pack src) of
        Left err -> error "Error parsing papers HTML"
        Right pan -> do
            let pans = justRows pan
            flip map pans $ \p -> do
                case runPure $ (writeHtml5String defaultHakyllWriterOptions) p of
                    Left err -> error "Error writing papers HTML"
                    Right txt -> unpack txt


justRows :: Pandoc -> [Pandoc] 
justRows (Pandoc m blocks) =
    splitTable table
  where
    table = head $ dropWhile (not . isTable) blocks
    isTable (Table _ _ _ _ _) = True 
    isTable _ = False 
    splitTable (Table i a d c rows) = 
        (Pandoc m . secondCell) <$> rows
    secondCell (_:x:_) = x

compileRecentPapers :: Int -> Compiler [String]
compileRecentPapers n = do
    take n <$> compilePapers

papersContext :: Context a
papersContext = listField "papers" defaultContext ps
  where
    ps :: Compiler [Item String]
    ps = (Item "" <$>) <$> compilePapers
    
recentPapersContext :: Context a
recentPapersContext = listField "recentpapers" defaultContext ps
  where
    ps :: Compiler [Item String]
    ps = (Item "" <$>) <$> compileRecentPapers 5

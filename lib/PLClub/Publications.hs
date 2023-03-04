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

-- | Run the entire `papers/Makefile` process and read one of the
-- generated files as a string
readFileAfterMaking :: String -> IO String
readFileAfterMaking fn = withSystemTempDirectory "plclub_bib" $ \f -> do
    copyFile "papers/Makefile" (f </> "Makefile")
    copyFile "papers/bold-title.bst" (f </> "bold-title.bst")
    callProcess "make" ["-C", f]
    readFile (f </> fn)

-- | Generate "plclub.html" as a String.
makePapersHtml :: IO String
makePapersHtml = readFileAfterMaking "plclub.html"

-- | Generate "plclub_bib.html"
makeBibHtml :: IO String
makeBibHtml = readFileAfterMaking "plclub_bib.html"

-- | Generate "merged.bib"
makeMergedBib :: IO String
makeMergedBib = readFileAfterMaking "merged.bib"

-- | Given the HTML of the generated file "plclub.html" as a String,
-- | compute a list of strings
parsePapers :: String -> [String]
parsePapers src = 
    case runPure $ readHtml defaultHakyllReaderOptions (pack src) of
        Left err -> error "Error parsing papers HTML"
        Right pandoc -> do
            let entries = parseMainTable pandoc
            flip map entries $ \entry -> do
                case runPure $ writeHtml5String defaultHakyllWriterOptions entry of
                    Left err -> error "Error writing papers HTML"
                    Right txt -> unpack txt

-- | Filter the document into a set of table bodies. Pandoc's AST
-- allows for tables to have multiple bodies in the form of a list,
-- but we hardcode the assumption that this list has length 1.
parseMainTable :: Pandoc -> [Pandoc]
parseMainTable (Pandoc m blocks) =
  (\blocks -> Pandoc m blocks) <$> (getRowsOf $ firstTableBody blocks)
  where
    firstTableBody blocks =
      case blocks of
        Table _attr _cap _colspec _head body foot : rest ->
          head body
        x : rest -> firstTableBody rest
        _ -> error "Did not find a 'Table' block in the provided Pandoc"

-- | Convert a 'TableBody' to a list of 'Pandoc' values. This function
-- assumes the table is in the format of "plclub.html," i.e. a table
-- whose rows' *second entries* contain HTML corresponding intuitively
-- corresponding to one "entry" in the list of papers.
getRowsOf :: TableBody -> [[Block]]
getRowsOf (TableBody _att _rhc _head rows) =
  secondCellOf <$> rows

-- | Given a table body 'Row', return the contents (a list of 'Block'
-- values) of the row's second cell
secondCellOf :: Row -> [Block]
secondCellOf (Row _attr cells) =
  case snd cells of
    Cell _attr _align _rsp _csp blocks -> blocks
  where
    snd (_:x: _) = x
    
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

-- | A compiler action that assembles the webpage in a temporary directory,
-- parses everything, and returns a list of strings
compilePapers :: Compiler [String]
compilePapers = do
    unsafeCompiler $ do
        html <- makePapersHtml
        return $ parsePapers html

compileRecentPapers :: Int -> Compiler [String]
compileRecentPapers n = do
    take n <$> compilePapers

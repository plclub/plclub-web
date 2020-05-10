{-# language OverloadedStrings #-}
{-|
 - Module: PLClub.PandocExtra
 - Description: Customized Pandoc things
 -}

module PLClub.PandocExtra where

import Data.Functor.Identity (runIdentity)
import System.IO.Unsafe (unsafePerformIO)
import Hakyll.Web.Pandoc (defaultHakyllWriterOptions
                         , defaultHakyllReaderOptions)
import Data.Text (Text)
import qualified Text.Pandoc as P
import Text.Pandoc.Options (WriterOptions (..)
                           , ReaderOptions (..))
import Hakyll
import Skylighting (SyntaxMap)
import Skylighting.Syntax (defaultSyntaxMap)
import qualified Skylighting as Sky
import qualified Data.Map as Map

-- Our map of recognized languages for code highlighting
-- We dynamically add our own lexers as Kate highlighting files
-- https://docs.kde.org/stable5/en/applications/katepart/highlight.html
-- Changes to syntax maps do not trigger site recompilation, you must rebuild
customSyntaxMap :: SyntaxMap
customSyntaxMap =
  Map.union defaultSyntaxMap extraMap
  where
    extraMap = unsafePerformIO $ do
      msm <- Sky.loadSyntaxesFromDir "extra/syntax/"
      case msm of
        Left err -> error $ "Encountered error while \
                            \ loading custom syntax files: " ++ err
        Right sm -> return sm

-- Our Pandoc writer configuration
-- We do __not__ use Pandoc for theming because Pandoc is used not used in its
-- standalone mode (i.e., does not produce a valid HTML file) and cannot insert
-- CSS. Instead we use Hakyll to compile Kate theme files into CSS and load that.
customWriterOptions :: WriterOptions
customWriterOptions =
  defaultHakyllWriterOptions
  { writerSyntaxMap = customSyntaxMap }

-- Our Pandoc reader configuration
customReaderOptions :: ReaderOptions
customReaderOptions = defaultHakyllReaderOptions

-- Compile a Kate .theme JSON file into a CSS file
kateThemeToCSSCompiler :: Compiler (Item String)
kateThemeToCSSCompiler = do
  contents <- getResourceLBS
  let mstyle = Sky.parseTheme (itemBody contents)
  case mstyle of
    Left err -> do
      fn <- getUnderlying
      error $ "Encountered error while parsing customized theme \
              \ file (\"" ++ toFilePath fn ++ "\"): " ++ err ++
              "\nAre you sure this is a Kate .theme file?"
    Right style -> do
      makeItem $ Sky.styleToCss style

-- | Pandoc configuration for generating an independent TOC
tocWriterOptions :: WriterOptions
tocWriterOptions =
  defaultHakyllWriterOptions
  { writerTableOfContents = True  
  , writerTOCDepth = 2 + 1
  , writerTemplate = Just tocTemplate
  }

-- | The template for blog posts (may crash at runtime)
-- This evaluates to the template blog posts at runtime, permitting niceties
-- like automatics Tables of Contents. It may through errors a runtime
-- (site compile) time if there is a problem with the template
tocTemplate :: P.Template Text
tocTemplate =
  let fpp = "" -- optional path for resolving partials
      template = P.compileTemplate fpp "$toc$"
  in
  case runIdentity template of
    Left err -> error $ "Error when generating TOC template: " ++
                  show err
    Right tem -> tem
        

makeTOC :: Compiler (Item String)
makeTOC =  pandocCompilerWith defaultHakyllReaderOptions tocWriterOptions

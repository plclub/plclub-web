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

import qualified Hakyll.Alectryon as Alectryon

-- Our map of recognized languages for code highlighting
-- We dynamically add our own lexers as Kate highlighting files
-- https://docs.kde.org/stable5/en/applications/katepart/highlight.html
-- Changes to syntax maps do not trigger site recompilation, you must rebuild
customSyntaxMap :: SyntaxMap
customSyntaxMap =
  Map.union extraMap defaultSyntaxMap
  where
    extraMap = unsafePerformIO $ do
      msm <- Sky.loadSyntaxesFromDir "extra/kate/syntax/"
      case msm of
        Left err -> error $ "Encountered error while \
                            \ loading custom syntax files: " ++ err
        Right sm -> return sm

-- Our Pandoc writer configuration
customWriterOptions :: WriterOptions
customWriterOptions =
  defaultHakyllWriterOptions
  { writerSyntaxMap = customSyntaxMap }

-- Our Pandoc reader configuration
customReaderOptions :: ReaderOptions
customReaderOptions = defaultHakyllReaderOptions

-- | Process Coq code using Alectryon, for posts with the @alectryon@ field set.
customPandocCompiler :: Alectryon.Options -> Compiler (Item String)
customPandocCompiler opt = do
  doc <- Alectryon.tryTransform opt =<< readPandocWith customReaderOptions =<< getResourceBody
  return (writePandocWith customWriterOptions doc)

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


-- | Return an representation of the TOC of the current item
-- __Caution__: This used to use the item returned by
-- 'getResourceString' but this caused Hakyll's caching mechanism to
-- overwrite the blogpost with the TOC because the resulting item had
-- the same identifier as the blog post item.
makeTOC :: Compiler (Item String)
makeTOC =  do
    itemtoc <- getItemToc
    renderPandocWith defaultHakyllReaderOptions tocWriterOptions itemtoc
  where
    getItemToc = do
      item <- getResourceString
      let origid = itemIdentifier item
          newid =  setVersion (Just "toc") origid
          body = itemBody item
      return (Item newid body)

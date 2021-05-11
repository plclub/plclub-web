---
title: "Winter is Coming -- Even Faster"
speaker: "Joachim Breitner"
semester: "SP21"
---
Abstract:
   Winter is a Haskell port of the reference implementation of
   WebAssembly, and I wanted to use it in one of my projects. It runs
   small examples just fine, but once they get a bit larger, it was
   just too slow. So I pulled out the profiler and went hunting for
   low-hanging fruit, and also less low-hanging fruit, plucking 7 in
   total:

    * Using Vectors instead of Lists
    * SPECIALIZE
    * Difference lists
    * Export lists
    * Eta-Expanding ReaderT
    * Simpler code
    * …and a zipper.

   In this talk I will show how I identified the bottle necks, how I
   solved them, and how big the gain was. All of this is real – I will
   be retracing the steps I took while solving a real problem I was
   facing.

Homework:
   Make yourself familiar with WebAssembly. Suggested reading is
   https://developer.mozilla.org/en-US/docs/WebAssembly/Concepts plus
   https://developer.mozilla.org/en-US/docs/WebAssembly/Understanding_the_text_format
or if you want something more lightweight, the blog post series at
https://hacks.mozilla.org/category/code-cartoons/a-cartoon-intro-to-webassembly/

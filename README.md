# PLClub Website

This iteration began in November 2019. The previous site had been maintained for at least 15 years and used OMake and Java. This version uses the Haskell library Hakyll.

## Dependencies

* The `stack` build tool for Haskell
* `bibtex2html` package
* `make`

## Build instructions

Because the site is deployed as static files, building is a 2-step process. First we build the executable (simply called `site`) and then we run `site` to build the website from the source files.

The compiler _should_ be able to build with just

	stack build

This will install all necessary Haskell libraries under `.stack-work/`, typically compiling them from scratch. It will also install a GHC binary. This process should only need to happen once. Be prepared to wait.

When the site is built we can run

	stack exec site -- build

to build the site. With

	stack exec site -- watch 

we can launch a live preview server at [http://localhost:8000](http://localhost:8000). The preview server will watch the source files and recompile on-the-fly. 

Sometimes it is necessary to recompile everything from scratch. In this case run

	stack exec site -- rebuild

## Adding information to the site

### Adding a new PL Club meeting

Look under _meetings_

### Adding a new person

(Not completely working yet. The front page currently is a static mock-up, while the _people_ page is built with Hakyll).

Look under _people_

### Recent publications

The recent publications is built by running a Makefile in a temporary directory and then parsing the results with Pandoc. This is hacky but works surprisingly well.

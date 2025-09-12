# PL Club Website

## Build instructions

### Dependencies
The following dependencies are required to build the website:

- [GHC](https://www.haskell.org/ghc/), the standard Haskell compiler
- [cabal-install](https://www.haskell.org/cabal/), a Haskell package
  management and build system. (This package provides the command-line
  utility `cabal`.)
- `make`
- [bibtex2html](https://www.lri.fr/~filliatr/bibtex2html/index.en.html),
  used to compile a list of PL Club publications from a set of `.bib`
  files.
- [pkg-config](https://www.freedesktop.org/wiki/Software/pkg-config/),
  required to build some of the Haskell dependencies

You may also require a working installation of
[Alectryon](https://github.com/cpitclaudel/alectryon) to build blog
posts that rely on Alectryon. However, Hakyll and Alectryon
intelligently generate cache files which then get checked into the git
repository, so Alectryon is only required to build new blog posts for
the very first time. Even a clean rebuild of the site should not
require Alectryon unless new literate Coq blog posts are added.

### Building and deploying

- `cabal build` to build the *Haskell package* that actually generates
  the HTML
- `cabal exec site -- build` to build the website HTML. This creates a
  local cache of the generated files.
- `cabal exec site -- rebuild` to clear the local Hakyll cache (except
  Alectyon-generated files) and build the site from scratch
- `cabal exec site -- deploy` to deploy the site to the public
  internet via ENIAC

Deploying the generated site to the internet requires SSH access to
the `plclub` account on ENIAC. This can only be performed from the
university network, so you need to connect to the university VPN first
if you are off campus. SSH access to ENIAC is limited, of course. If
you think you require SSH access, ask the website maintainers.

### Building with Nix

A Nix flake is provided. Currently, `nix develop` should drop you into
a shell suitable for running the above commands. Be prepared to wait a
long time during the first site build.

## Build instructions

## FAQ

### How do I talk to about...?
Questions about the content of the website are best directed to
Cassia Torczon. When in doubt, ask in the *#website* channel on the PL
Club Slack.

### How do I contribute?
Information about contributing and maintaining this website can be found in the
[Wiki](https://github.com/plclub/plclub-web/wiki).

You can always ask the friendly maintainers in the *#website* channel
on the PL club Slack.

### Where is the old website?

Work on the current version of the website began late November 2019,
with deployment around February 2020. The previous version (as seen on
the [Wayback
machine](https://web.archive.org/web/20191217223927/https://www.cis.upenn.edu/~plclub/))
had been in service for about 15 years and used OMake and Java. A tar
archive of the old website can be found in the home directory of the
`plclub` user on ENIAC.

### Where do I find the PL Club logo?

The nicely formatted SVG logo was created by [Daniel
Wagner](http://dmwit.com/plclub-logo/) to replace an earlier PNG
version of unknown provenance. The SVG logo, as well as large and
small PNG files rendered from it, are found under `img/`.

The original PL Club logo is at least as old as the website itself, so
around since at least 2005.

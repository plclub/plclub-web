############################################################################
#
#  Primary targets:
#    all           - synonym for 'coq' and the default target
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes all generated files
#
#  Other targets (intended to be used by the developers of this library):
#    ea            - the target used to generate and update
#                    AtomEnv.v when AssocList.v is modified.
#    dist          - builds a distribution file called dist.zip
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

## Directory where generated HTML documentation should go.

DOCDIR = doc/html

## List of files to be compiled and documented.

FILES = \
	AdditionalTactics \
	AssocList \
	Atom \
	AtomEnv \
	AtomSet \
	FSetWeakDecide \
	FSetWeakNotin \
	ListFacts \
	Metatheory

## Lists calculated from the above.

VFILES  = $(foreach i, $(FILES), $(i).v)
VOFILES = $(foreach i, $(FILES), $(i).vo)


############################################################################

.PHONY: all clean doc coq documentation
.SUFFIXES: .v .vo

all: coq

coq: $(VOFILES)

doc:
	make documentation

documentation: $(DOCDIR) $(VFILES)
	$(COQDOC) -g --quiet --noindex --utf8 --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)


############################################################################

%.vo: %.v
	$(COQC) -q -I . $<

$(DOCDIR)/%.html: %.v $(DOCDIR)

$(DOCDIR):
	mkdir -p $(DOCDIR)


############################################################################

.depend: $(VFILES)
	$(COQDEP) -I . $(VFILES) > .depend

include .depend

############################################################################

ifneq ($(origin DATE),undefined)
DIR = metatheory-$(DATE)
else
DIR = metatheory-bogus
endif

ea: AssocList.v
	python translate.py AssocList.v > AtomEnv.v

dist:
	svn export . $(DIR)
	(cd $(DIR); make documentation)
	rm -rf $(DIR)/doc/dists
	echo Release $(DATE) / svn revision `svnversion .` >> $(DIR)/VERSION
	zip -r $(DIR).zip $(DIR)
	@echo
	@echo Done.
	@echo See $(DIR) and $(DIR).zip.

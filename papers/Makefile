B2HFLAGS = -dl \
	   -s bold-title \
	   --nodoc -nofooter -noheader --no-abstract -nokeys -use-table --no-keywords\
	   --named-field slides slides \
	   --named-field full 'full version' \
	   --named-field short 'short version' \
	   --named-field prelim 'preliminary version' \
	   --named-field conf 'conference version' \
	   --named-field official 'official version' \
	   --named-field homepage 'home page' \
	   --named-field manuscript 'manuscript' \
	   --named-field TR 'tech report' \
	   --named-field errata 'errata' \
	   --named-field sources 'source code' \
	   --debug \
	   --reverse-sort --sort-by-date

MV=mv
BIBS=bcp.bib weirich.bib zdancewic.bib alur.bib obastani.bib

.DELETE_ON_ERROR: $(BIBS)

plclub.html: merged.bib Makefile
	bibtex2html -o plclub $(B2HFLAGS) -citefile plclub.keys ./merged.bib

merged.bib: $(BIBS)
	bib2bib -s -r -oc plclub.keys -ob merged.bib -c 'bcp:"yes"|plclub:"yes"' $(BIBS)

bcp.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~bcpierce/papers/bcp.bib
	bib2bib -ob $@-tmp -c 'not($$key = "poplmark") and not($$key = "AITR-474")' $@
	$(MV) $@-tmp $@

weirich.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~sweirich/weirich.bib

zdancewic.bib:
	-$(RM) $@
	wget http://www.cis.upenn.edu/~stevez/papers/zdancewic.bib
	bib2bib -ob $@-tmp -c 'not($$key = "ABFF+05")' $@
	$(MV) $@-tmp $@

alur.bib:
	-$(RM) $@
	wget https://dblp.uni-trier.de/pid/a/RAlur.bib?param=1 -O alur.bib

obastani.bib:
	-$(RM) $@
	wget https://dblp.org/pid/21/11275.bib?param=1 -O obastani.bib

clean:
	-$(RM) bib2html* plclub.keys plclub.html plclub_bib.html $(BIBS) merged.bib

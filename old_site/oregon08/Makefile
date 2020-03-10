publish:
	rsync -azvP -e ssh --delete --exclude coq-tutorial --exclude \*.svn ./ plclub@eniac.seas.upenn.edu:html/oregon08

dist:
	rm -rf coq-tutorial
	svn export tutorial coq-tutorial
	(cd coq-tutorial ; make documentation)
	rm -f coq-tutorial.zip
	zip -r coq-tutorial.zip coq-tutorial

perms:
	chmod -R og+rX .

TOOL=maxcomp
VERSION = 1.6

all:
	ghc -O -Wall -o $(TOOL) Main

clean:
	rm -f *.hi *.o $(TOOL) Main

archive:
	git archive --format=tar --prefix=$(TOOL)/ HEAD | gzip > $(TOOL)-$(VERSION).tgz

TOOL=moca
VERSION=0.3
all:
	stack install

clean:
	rm -f *.hi *.o $(TOOL) 

archive:
	git archive --format=tar --prefix=$(TOOL)/ HEAD | gzip > $(TOOL)-$(VERSION).tgz

static:
	ghc -optl -fuse-ld=bfd -O -Wall -optl-static -o $(TOOL)-static Main

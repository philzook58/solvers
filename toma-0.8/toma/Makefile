TOOL=toma
VERSION=0.8

all:
	cabal build
	cp `cabal list-bin $(TOOL)` .

static:
	docker build --output type=local,dest=. -t toma-static .

clean:
	rm -f *.hi *.o $(TOOL) $(TOOL)-static

archive:
	git archive --format=tar --prefix=$(TOOL)/ HEAD | gzip > $(TOOL)-$(VERSION).tgz

default: plugin

plugin: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq:
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra-phony 'distclean' 'clean' \
	    'rm -f $$(join $$(dir $$(VFILES)),$$(addprefix .,$$(notdir $$(patsubst %.v,%.aux,$$(VFILES)))))'

clean:
	$(MAKE) -f Makefile.coq distclean
	rm -f Makefile.coq

install:
	$(MAKE) -f Makefile.coq install

.PHONY: default plugin clean install

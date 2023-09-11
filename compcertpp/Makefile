include Makefile.verbosity

.PHONY: clean mrproper cleandoc cleantar all proof doc distclean archive tar tgz tbz2

.SUFFIXES: .html .vo .v .dep .hdr .tar .tbz2 .tgz .tgt

all: proof doc archive

proof:
	@echo WARNING: estimated compilation time more than 2 hours. Do you wish to continue ? '('y/N')'
	read r && if test "$$r" = "y" ; then for f in *.src ; do make $$(basename $$f .src).tgt ; done ; else echo Abort ; exit 2 ; fi ; done

doc: coq2html.ml
	for f in *.v ; do test -e $$(basename $$f .v).glob || echo Missing $$(basename $$f .v).glob: no links available in $$(basename $$f .v).html ; done
	ocaml str.cma coq2html.ml -o %.html *.glob *.v
	for f in *.htm ; do cp $$f $$(basename $$f .htm).html ; done
	if test -e index.html.default ; then cp index.html.default index.html ; fi

archive: tbz2

tar:
	for f in *.src ; do make $$(basename $$f .src).tar ; done

tgz:
	for f in *.src ; do make $$(basename $$f .src).tgz ; done

tbz2:
	for f in *.src ; do make $$(basename $$f .src).tbz2 ; done

%.tgt:
	touch $@

%.vo: %.v
	coqc $(VERBOSITY) $<

coq2html.ml: coq2html.mll
	ocamllex $<

cleandoc:
	rm -f *.html coq2html.ml

cleantar:
	rm -f *.tar *.tgz *.tbz2 *.dep .depend

clean: cleandoc cleantar

mrproper: clean
	rm -f *.vo .depend *.hdr *.tgt

distclean: mrproper
	rm -f *.glob

%.dep:
	(cat /dev/null $^; echo $(basename $@)) | sort | uniq > $@

.depend: *.v
	coqdep -I . *.v > .depend
	sed 's/\.vo: [^ ]*\.v/\.vo:/' .depend | sed 's/\.vo/\.v/g' | sed 's/\.v/\.dep/g' > .depend.aux
	grep 'Header.vo:' .depend | sed 's!.vo: [^ ]*\.v!\.hdr:!' | sed 's!Header\.v!Header\.hdr!g' | sed 's!^\(.*\)\.hdr: !\1.hdr: \1.v !' >> .depend.aux
	grep -v 'Header.vo:' .depend | sed 's!Header.v!Header.hdr!g' >> .depend.aux
	mv .depend.aux .depend
	for f in *.src ; do echo -n $$(basename $$f .src).tar: ' ' ; cat $$f | while read i ; do echo -n $$i.dep ' ' ; done ; echo ; done >> .depend
	for f in *.src ; do echo -n $$(basename $$f .src).tgt: ' ' ; cat $$f | while read i ; do echo -n $$i.vo ' ' ; done ; echo ; done >> .depend

%.hdr:
	touch $@

%.tar:
	rm -f $(basename $@)
	ln -s . $(basename $@)
	tar chf $@ $(basename $@)/README $(basename $@)/coq2html.mll $(basename $@)/coq2html.css $(basename $@)/coq2html.js $(basename $@)/Makefile  $(basename $@)/Makefile.verbosity $(basename $@)/$(basename $@).src  $(basename $@)/$(basename $@).htm
	cat $^ | sort | uniq | while read i ; do tar rhf $@ $(basename $@)/$$i.v ; if test -e $$i.glob ; then tar rhf $@ $(basename $@)/$$i.glob ; else echo $$i.glob missing ; fi ; done
	if test -e $(basename $@).lst ; then cat $(basename $@).lst | { error=0 ; while test $$error -eq 0 && read f ; do tar rhf $@ $(basename $@)/$$f ; error=$$? ; done ; if test $$error -ne 0 ; then exit $$error ; fi ; tar rhf $@ $(basename $@)/$(basename $@).lst ; } ; fi
	if test -e index.html.default ; then tar rhf $@ $(basename $@)/index.html.default ; else cp $(basename $@).htm index.html.default && tar rhf $@ $(basename $@)/index.html.default && rm index.html.default ; fi
	rm -f $(basename $@)

%.tbz2: %.tar
	bzip2 -c $< > $@

%.tgz: %.tar
	gzip -c $< > $@

-include .depend

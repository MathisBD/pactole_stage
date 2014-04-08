# rebuilds the makefile, using coq_makefile + some hack to maintain a
# different makefile.

coq_makefile -f _CoqProject -o Makefile

sed -i '/mkdir -p html/a\
	rm -f html/coqdoc.css' Makefile

sed -i '/-d html/a\
	cd html; ln -sf ../coqdoc.css' Makefile

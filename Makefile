all: main

test: main
	./main Essai.class
	./main soot-2.5.0.jar
	./main apache-ivy-2.5.0/ivy-2.5.0.jar
	./main jtopas-jt.jar
	./main jtopas.jar

LIBS =unix.cma zip.cma extLib.cma str.cma javalib.cma sawja.cma 
main: main.ml cfg.ml dom.ml
	ocamlfind ocamlc -g $(LIBS) -package sawja cfg.ml dom.ml main.ml -o main

Essai.class: Essai.java
	javac Essai.java

.PHNY:
clean:
	rm -f *~ *.class main *.cmi *.cmo 
	rm -f results.csv


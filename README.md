Getting the Uniqueness as Separation project compiled. On the terminal: 

1. Create a new switch called coq8-11-2 with the following ocaml compatible version.
	opam switch create coq8-11-2 4.07.1

2. Update environment
	eval $(opam env)

3. Install Coq 8.11.2 and set the switch
	opam pin add coq 8.11.2

4. Add repo
	opam repo add coq-released https://coq.inria.fr/opam/released

5. Install ssreflect  1.12.0  (CoqUtils dependency) 
	opam install coq-mathcomp-ssreflect.1.12.0

6. Install fingroup 1.12.0  (CoqUtils dependency)
	opam install coq-mathcomp-fingroup.1.12.0

7. Install algebra 1.12.0  (CoqUtils dependency)
	opam install coq-mathcomp-algebra.1.12.0

8. Install deriving - Download repo from https://github.com/arthuraa/deriving
	make
	make install

9. Install extructures
	opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
	opam install coq-deriving
	opam install coq-extructures.0.3.0
	

	Note: Deriving & extructures can also be installed in the following way 
	Download from https://github.com/arthuraa/extructures 
	make
	make install

10. Install Coq-utils from https://github.com/arthuraa/coq-utils
	make
	make install

11. Go to the Artifact folder and do
	make


The instructions were tested in MacOS Sequoia 15.5 and Linux Mint 20.2 Cinnamon (Kernel 5.13.0-21-generic).

## Compiling the Mixed-Safety Verification project. 


Before starting, make sure opam is installed:  
	`opam --version`  

If opam has not been initialise on your system, run:  
	`opam init`  

and update the shell environment with:  
	`eval $(opam env)`  

Then follow these steps on the terminal:  
 
1. Create a directory (e.g mixed-safety-ws) for the project files and move into it:  
	`mkdir mixed-safety-ws`  
	`cd mixed-safety-ws`  

2. Create a new opam switch named coq8-11-2 with Ocaml version 4.10.2:  
	`opam switch create coq8-11-2 4.10.2`  

3. Activate the switch in the current environment:  
	`eval $(opam env --switch=coq8-11-2)`  

4. Install and pin Coq version 8.11.2:    
	`opam pin add coq 8.11.2`  

5. Add the Coq release packages repository:  
	`opam repo add coq-released https://coq.inria.fr/opam/released`  

   Add the extra development repository:  
	`opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev`  

6. Install Mathcomp dependencies ssreflect version 1.12.0, fingroup 1.12.0 and algebra 1.12.0 (CoqUtils dependencies):   
	`opam install coq-mathcomp-ssreflect.1.12.0`  
	`opam install coq-mathcomp-fingroup.1.12.0`  
	`opam install coq-mathcomp-algebra.1.12.0`  

7. Install aditional dependencies deriving and extructures:  
	`opam install coq-deriving.0.1.1`  
	`opam install coq-extructures.0.3.0`  
	
8. Install Coq-utils:  
	`git clone https://github.com/arthuraa/coq-utils.git`  
	`cd coq-utils`  
	`make`  
	`make install`  

9. Return to the parent directory:  
	`cd ..`  

10. Download and compile the project:  
	`git clone https://github.com/selenelinares/mixed-safety-verification`  
	`cd mixed-safety-verification`  
	`make`  


These instructions were tested on:   
- MacOS Sequoia 15.5 on Apple M1 pro
- MacOS Tahoe 26.3.1 on Apple M5 and 
- Linux Mint 20.2 Cinnamon (Kernel 5.13.0-21-generic).

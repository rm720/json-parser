This docs is how I bilt and compiled cake ML program:

1. Install Poly ML. latest veriosion for today (22-12-2023) is v5.9.1 
	Git fork, git clone https://github.com/polyml/polyml
	To build:
	```sh
	cd polyml
	./configure
	make
	make install
	```

2. HOL
	Used regression test https://cakeml.org/regression.cgi
	Particular one
	https://cakeml.org/regression.cgi/job/2255
	Commits:
	Job 2255
	CakeML:
	4561273aac7c5290fd1b072cc5090dad1275891d
	Merging into:
	4ce61c307e8542262db1b33ca6bbaba2473fd1e0
	HOL:
	d587e1c70b4c059edc079ed4a529b5b7423223b8

	Followed the guide here https://github.com/HOL-Theorem-Prover/HOL/blob/develop/INSTALL

	.zshrc
	# Library paths
	declare -x LD_LIBRARY_PATH="/usr/local/lib:$HOME/lib"
	# Development directories
	declare -x HOLDIR="/Users/ra/repos/HOL"
	declare -x CAKEMLDIR="/Users/ra/repos/cakeml"

	```sh
	cd $HOLDIR
	poly < tools/smart-configure.sml
	$HOLDIR/bin/build
	```

	to patch the error /usr/local/bin/polyc: line 51: g++ -std=gnu++11: command not found
	changed in /usr/local/bin/polyc
	LINK="g++ -std=gnu++11"
	for
	LINK="g++-11"

	put 
	(load "/Users/ra/repos/HOL/tools/hol-mode")
	(load "/Users/ra/repos/HOL/tools/hol-unicode")
	in 
	~/.emacs

3. Compile (Create) .S file 
	```sh
	cd cakeML/tutorial/solutions
	Holmake
	```

4. Compile executable

	I could not find a working cakeML compiler for ARMv8 architecture, so I used an AWS linux machine.

	go to Amazon EC2 dashboard
	https://ap-southeast-2.console.aws.amazon.com/ec2/home?region=ap-southeast-2#Instances:instanceState=running

	To connect:
	ssh -i "/Users/ra/.ssh/aws-key-1.pem" ubuntu@ec2-13-239-2-20.ap-southeast-2.compute.amazonaws.com

	Then
	increase memory by using a swap of 15G with 1M block:
	sudo swapon --show
	sudo dd if=/dev/zero of=/swapfile bs=1M count=15360
	sudo chmod 600 /swapfile
	sudo mkswap /swapfile
	sudo swapon /swapfile
	sudo swapon --
	free -
	echo '/swapfile none swap sw 0 0' | sudo tee -a /etc/fstab
	cat /proc/sys/vm/swappiness


	** compiling .CML file **
	scp -i "/Users/ra/.ssh/aws-key-1.pem" /Users/ra/repos/play-cakeML/cake-x64-64/hello.cml ubuntu@ec2-13-239-2-20.ap-southeast-2.compute.amazonaws.com:/home/ubuntu/repos/cake-x64-64/

	cd /home/ubuntu/repos/cake-x64-64
	make hello.cake
	./hello.cake

	** compiling .S file
	unpack and compile .S file to cakeML.

	scp -i "/Users/ra/.ssh/aws-key-1.pem" /Users/ra/repos/election-verification/src/cake/crypto.S ubuntu@ec2-13-239-2-20.ap-southeast-2.compute.amazonaws.com:/home/ubuntu/repos/cake-x64-64/

	to compile:
	make clean cc cake.S basis_ffi.c   -D__EVAL__ -o cake
	cc crypto.S basis_ffi.c -o crypto

	cc wordfreq.S basis_ffi.c -o crypto

	to run:
	./crypto
	or
	./wordfreq mytext.txt 

	For every executable program you need 3 files in one directory:
	SomethingProgPcropt.sml
	SomethingProofScript.sml
	SomethingCompileScript.sml
	and Holmake file with all the paths of the libraries used
	Run Holmake in the directory
	This will compile all the required (imported) packages and create 3 .sig files 
	and one Something.S file.
	After that you need to compile executable using bootstraped compiler, i.e. in cake-x64-64 


	python3.12 -m venv myenv
	source myenv/bin/activate
	deactivate


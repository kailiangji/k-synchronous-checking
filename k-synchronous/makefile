FILES=`ls *.pml`

all:
	@for file in $(FILES); do \
		spin -a $$file; \
		gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c; \
		./pan -m1000000  -E -n; \
	done

e:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
c:
	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
s:
	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
o:
	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
g:
	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

dfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
e-dfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
c-dfs:
	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
s-dfs:
	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
o-dfs:
	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n
g-dfs:
	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

bs-dfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
e-bs-dfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
c-bs-dfs:
	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
s-bs-dfs:
	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
o-bs-dfs:
	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
g-bs-dfs:
	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

bs-bfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
e-bs-bfs:
	spin -a elevator.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
c-bs-bfs:
	spin -a commit_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
s-bs-bfs:
	spin -a storage_protocol.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
o-bs-bfs:
	spin -a osr.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n
g-bs-bfs:
	spin -a german.pml
	gcc -DMEMLIM=15024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DBITSTATE -w -o pan pan.c
	./pan -m1000000  -E -n

clean:
	@rm -f pan*
	@rm -f *.trail
	@echo Clean Done

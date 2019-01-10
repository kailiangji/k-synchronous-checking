FILES=`ls *.pml`

all:
	@touch log
	@for file in $(FILES); do \
    		spin -a  $$file; \
		gcc -DMEMLIM=6024 -O2 -DBFS -DXUSAFE -DSAFETY -DNOCLAIM -DCOLLAPSE -w -o pan pan.c; \
		./pan -m1000000  -E -n > log;\
	done
	@rm log
	@rm -f pan*
clean:
	@rm -f *.trail
	@echo Clean Done

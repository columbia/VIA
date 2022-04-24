#!/bin/bash                                                                                                                                                                       
#!/bin/bash

SRV=$1

for i in `seq 1 4`; do
	ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "cd kvmperf/localtests; ./kernbench.sh"
	echo "Grab results for $SRV"
	ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "cd kvmperf/localtests; cat kernbench.txt; rm kernbench.txt" >> kern.txt
done

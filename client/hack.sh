#!/bin/bash                                                                                                                                                                       

SRV=$1
for i in `seq 1 4`; do
       ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "cd kvmperf/localtests; ./hackbench.sh 20"
       echo "Grab results for $SRV" 
       ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "cd kvmperf/localtests; cat hackbench.txt; rm hackbench.txt" >> hack.txt
done

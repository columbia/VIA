#!/bin/bash

YCSB_PATH=./ycsb-0.17.0
YCSB=$YCSB_PATH/bin/ycsb

SRV=$1
REPTS=${2-5}

for i in `seq 1 $REPTS`; do
	$YCSB run redis -s -P $YCSB_PATH/workloads/workloada -p "redis.host=$SRV" -p "redis.port=6379" -P redis.param | tee >(grep "Throughput" | awk '{ print $3 }' >> redis.txt)
done

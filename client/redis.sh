#!/bin/bash

YCSB_PATH=./ycsb-0.17.0
YCSB=$YCSB_PATH/bin/ycsb

SRV=$1
REPTS=${2-10}
WORKLOAD=${3-rb}

run-ycsb() {
	$YCSB load redis -s -P $YCSB_PATH/workloads/workloada -p "redis.host=$SRV" \
		-p "redis.port=6379"
	
	for i in `seq 1 $REPTS`; do
		$YCSB run redis -s -P $YCSB_PATH/workloads/workloada -p "redis.host=$SRV" \
			-p "redis.port=6379" -P redis.param | \
			tee >(grep "Throughput" | awk '{ print $3 }' >> redis.txt)
	done
}

run-redis-bench() {
	for i in `seq 1 $REPTS`; do
		redis-benchmark -h $SRV -q -t get,set --csv -P 12 -n 1000000 | \
			tee >(awk -F',' '{gsub(/"/, "", $2); print $2 }' >> redis.txt)
	done
	#for i in `seq 1 $REPTS`; do
	#	redis-benchmark -h $SRV -q -t set --csv -P 12 -n 1000000 | \
	#		tee >(awk -F',' '{gsub(/"/, "", $2); print $2 }' >> redis-set.txt)
	#done

}

if [ $WORKLOAD == rb ]; then
	run-redis-bench
else
	run-ycsb
fi

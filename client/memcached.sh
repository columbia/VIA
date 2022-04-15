#!/bin/bash

set +x

YCSB_PATH=./ycsb-0.17.0
YCSB=$YCSB_PATH/bin/ycsb

MEMTIER_PATH=./memtier_benchmark/memtier_benchmark

SRV=$1
REPTS=${2-5}
WORKLOAD=${3-memtier}

run_ycsb()
{
	$YCSB load memcached -s -P $YCSB_PATH/workloads/workloada \
		-p "memcached.hosts=$SRV:11211"

	for i in `seq 1 $REPTS`; do
		$YCSB run memcached -s -P $YCSB_PATH/workloads/workloada -p \
			"memcached.hosts=$SRV:11211" -P memcached.param | \
			tee >(grep "Throughput" | awk '{ print $3 }' >> memcached.txt)
	done

}


run_memtier()
{
	for i in `seq 1 $REPTS`; do
		$MEMTIER_PATH --hide-histogram -p 11211 \
			-P memcache_binary -s $SRV 2>&1 | \
	                tee >(grep 'Totals' | awk '{ print $2 }' >> memcached.txt)
	done
}

if [ $WORKLOAD == memtier ]; then
	echo "Benchmark using memtier_benchmark"
	run_memtier
else
	echo "Benchmark using ycsb"
	run_ycsb
fi

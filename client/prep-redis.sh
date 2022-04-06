#!/bin/bash                                                                                                                                                                       
SRV=$1

YCSB_PATH=./ycsb-0.17.0
YCSB=$YCSB_PATH/bin/ycsb

ssh -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null $SRV "service redis-server start"

$YCSB load redis -s -P $YCSB_PATH/workloads/workloada -p "redis.host=$SRV" -p "redis.port=6379"

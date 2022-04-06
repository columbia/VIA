#!/bin/bash                                                                                                                                                                       

YCSB_PATH=./ycsb-0.17.0
YCSB=$YCSB_PATH/bin/ycsb

SRV=$1

ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "service mongodb start"
$YCSB load mongodb -s -P $YCSB_PATH/workloads/workloada -p "mongodb.url=mongodb://$SRV:27017/ycsb3" -threads 16

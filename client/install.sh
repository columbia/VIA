#!/bin/bash

echo "Downloading YCSB"
curl -O --location https://github.com/brianfrankcooper/YCSB/releases/download/0.17.0/ycsb-0.17.0.tar.gz
tar xfvz ycsb-0.17.0.tar.gz

sleep 1
echo "Downloading memtier_benchmark"

git clone https://github.com/RedisLabs/memtier_benchmark.git --branch v1.2.11
pushd memtier_benchmark
autoreconf -ivf
./configure
make
popd

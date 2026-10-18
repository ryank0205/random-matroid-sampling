# random-matroid-sampling
An algorithm to sample random matrix realisations for matroids. Starting with random full-rank matrices, operations on samples introduce dependencies, aiming to sample a wide variety of matroid structures.


How to use random_matroid_sampler.jl

smoke_test()
tests all functions work properly

sample_matroid(5, 10)
samples a random 5 x 10 matrix realisation using the matroid sampling algorithm

non_bases(A)
returns all k-element subsets of A that are linearly dependent


How to use benchmark_matroids.jl

benchmark(1000, 5, 10; prefix="test", progress_every=100)
generates 1000 matrices using both a simple random sampler and our algorithm and outputs the number of distinct isomorphism classes sampled, percentage of non-uniform samples, class frequencies and computation times. stores sampled data including a catalogue of matroid isomorphism classes reached in csv files prefixed "test". progress updates every 100 samples

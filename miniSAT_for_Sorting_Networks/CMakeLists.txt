cmake_minimum_required(VERSION 3.3)
project(minisat_for_snw_2)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

set(SOURCE_FILES
    core/Dimacs.h
    core/Main.cc
    core/Solver.cc
    core/Solver.h
    core/SolverTypes.h
    mtl/Alg.h
    mtl/Alloc.h
    mtl/Heap.h
    mtl/IntTypes.h
    mtl/Map.h
    mtl/Queue.h
    mtl/Sort.h
    mtl/Vec.h
    mtl/XAlloc.h
    simp/Main.cc
    simp/SimpSolver.cc
    simp/SimpSolver.h
    utils/Options.cc
    utils/Options.h
    utils/ParseUtils.h
    utils/System.cc
    utils/System.h)

add_executable(minisat_for_snw_2 ${SOURCE_FILES})
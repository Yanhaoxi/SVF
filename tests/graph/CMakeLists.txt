cmake_minimum_required(VERSION 3.23)
project(LOPAGraphTests LANGUAGES C CXX)

find_package(SVF CONFIG REQUIRED)

add_executable(vdg_scc_representative vdg_scc_representative.cpp)
target_compile_features(vdg_scc_representative PRIVATE cxx_std_17)
target_link_libraries(vdg_scc_representative PRIVATE SVF::SvfCore SVF::SvfLLVM)

add_executable(profile_self_loops profile_self_loops.cpp)
target_compile_features(profile_self_loops PRIVATE cxx_std_17)
target_link_libraries(profile_self_loops PRIVATE SVF::SvfCore SVF::SvfLLVM)

add_executable(pus_memory_map pus_memory_map.cpp)
target_compile_features(pus_memory_map PRIVATE cxx_std_17)
target_link_libraries(pus_memory_map PRIVATE SVF::SvfCore)

add_executable(pus_graph_lifecycle pus_graph_lifecycle.cpp)
target_compile_features(pus_graph_lifecycle PRIVATE cxx_std_17)
target_link_libraries(pus_graph_lifecycle PRIVATE SVF::SvfCore)

enable_testing()
add_test(NAME vdg_scc_representative COMMAND vdg_scc_representative)
add_test(NAME profile_self_loops COMMAND profile_self_loops)
add_test(NAME pus_memory_map COMMAND pus_memory_map)
add_test(NAME pus_graph_lifecycle COMMAND pus_graph_lifecycle)

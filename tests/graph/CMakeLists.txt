cmake_minimum_required(VERSION 3.23)
project(LOPAGraphTests LANGUAGES C CXX)

find_package(SVF CONFIG REQUIRED)

add_executable(vdg_scc_representative vdg_scc_representative.cpp)
target_compile_features(vdg_scc_representative PRIVATE cxx_std_17)
target_link_libraries(vdg_scc_representative PRIVATE SVF::SvfCore SVF::SvfLLVM)

enable_testing()
add_test(NAME vdg_scc_representative COMMAND vdg_scc_representative)

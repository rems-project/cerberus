cmake_minimum_required(VERSION 3.20)
project(ci_tests)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set (RC_ENABLE_GTEST ON)

file(GLOB_RECURSE SRC ../../runtime/libcn/src/*.c decorated/*.c test/*.cpp)

include(FetchContent)
FetchContent_Declare(
  googletest
  URL https://github.com/google/googletest/archive/03597a01ee50ed33e9dfd640b249b4be3799d395.zip
  DOWNLOAD_EXTRACT_TIMESTAMP true
)
# For Windows: Prevent overriding the parent project's compiler/linker settings
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

enable_testing()

include(GoogleTest)

FetchContent_Declare(
  rapidcheck
  GIT_REPOSITORY https://github.com/emil-e/rapidcheck.git
)
FetchContent_MakeAvailable(rapidcheck)

add_executable(ci_tests ${SRC})

target_link_libraries(ci_tests GTest::gtest_main rapidcheck rapidcheck_gtest)

target_include_directories(ci_tests PRIVATE ../../runtime/libcn/include)

gtest_discover_tests(ci_tests)

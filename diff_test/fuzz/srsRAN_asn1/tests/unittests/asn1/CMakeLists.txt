#
# Copyright 2021-2025 Software Radio Systems Limited
#
# This file is part of srsRAN
#
# srsRAN is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as
# published by the Free Software Foundation, either version 3 of
# the License, or (at your option) any later version.
#
# srsRAN is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Affero General Public License for more details.
#
# A copy of the GNU Affero General Public License can be found in
# the LICENSE file in the top-level directory of this distribution
# and at http://www.gnu.org/licenses/.
#

include_directories(../../..)

set_directory_properties(PROPERTIES LABELS "asn1")

add_executable(asn1_utils_test asn1_utils_test.cpp)
target_link_libraries(asn1_utils_test asn1_utils srsran_support gtest gtest_main)
add_test(asn1_utils_test asn1_utils_test)

add_executable(asn1_rrc_nr_test asn1_rrc_nr_test.cpp)
target_link_libraries(asn1_rrc_nr_test asn1_utils srsran_support rrc_nr_asn1 gtest gtest_main)
gtest_discover_tests(asn1_rrc_nr_test)

add_executable(main_test main_test.cpp util.cpp)
target_link_libraries(main_test asn1_utils srsran_support rrc_nr_asn1 gtest gtest_main)
# gtest_discover_tests(asn1_rrc_nr_test)


// use asnfuzz_rrc_uper::generate_rrc_messages;

// fn main() {
//     let encoded_message = generate_rrc_messages::generate_wrapped_security_mode_command();
//     std::fs::write("bin_output/rrc_smc_exp/wrapped_security_mode_command.bin", encoded_message)
//         .expect("Unable to write file");
//     println!("Encoded message saved to wrapped_security_mode_command.bin");
// } // -> generate_rrc_messages.rs


// use asnfuzz_rrc_uper::rrc_smc::SecurityModeCommand;
//
// fn main() {
//     // Generate a random SecurityModeCommand
//     let random_security_mode_command = SecurityModeCommand::random();
//
//     // Output or further process the generated SecurityModeCommand
//     println!("{:?}", random_security_mode_command);
// } // -> rrc_smc.rs


// use asnfuzz_rrc_uper::iterate_rrc_smc;
// use std::fs;
// use std::path::Path;

// fn main() {
//     let encoded_messages = iterate_rrc_smc::generate_security_mode_command_variants();

//     // Ensure the bin_output directory exists
//     let output_dir = "./bin_output";
//     if !Path::new(output_dir).exists() {
//         fs::create_dir(output_dir).expect("Failed to create bin_output directory");
//     }

//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("{}/wrapped_security_mode_command_{}.bin", output_dir, index + 1);
//         fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// }  // -> iterate_rrc_smc.rs




// use asnfuzz_rrc_uper::rrc_smc_entropic::generate_multiple_security_mode_commands;
// use std::fs;
// use std::path::Path;
// fn main() {
//     let encoded_messages = generate_multiple_security_mode_commands(100); // Generate 100 messages
//
//     // Save messages to files
//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("bin_output/wrapped_security_mode_command_{}.bin", index + 1);
//         std::fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// } // -> rrc_smc_entropic.rs




// use asnfuzz_rrc_uper::rrc_reest_req_entropic::generate_multiple_rrc_reestablishment_requests;
// use std::fs;
// use std::path::Path;
//
// fn main() {
//     // Ensure the output directory exists
//     let output_dir = "./bin_output";
//     if !Path::new(output_dir).exists() {
//         fs::create_dir(output_dir).expect("Failed to create bin_output directory");
//     }
//
//     // Generate 100 RRCReestablishmentRequest messages
//     let encoded_messages = generate_multiple_rrc_reestablishment_requests(100);
//
//     // Save messages to files
//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("{}/rrc_reestablishment_request_{}.bin", output_dir, index + 1);
//         fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// }




// use asnfuzz_rrc_uper::rrc_reest_comp_entropic::generate_multiple_rrc_reestablishment_completes;
// use std::fs;
// use std::path::Path;
//
// fn main() {
//     // Ensure the output directory exists
//     let output_dir = "./bin_output/rrc_reest_comp";
//     if !Path::new(output_dir).exists() {
//         fs::create_dir(output_dir).expect("Failed to create bin_output directory");
//     }
//
//     // Generate 100 RRCReestablishmentComplete messages
//     let encoded_messages = generate_multiple_rrc_reestablishment_completes(100);
//
//     // Save messages to files
//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("{}/rrc_reestablishment_complete_{}.bin", output_dir, index + 1);
//         fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// } //


// use asnfuzz_rrc_uper::measurement_report_entropic::generate_multiple_measurement_reports;
// use std::fs;
// use std::path::Path;
//
// fn main() {
//     // Ensure the output directory exists
//     let output_dir = "./bin_output/measurement_report";
//     if !Path::new(output_dir).exists() {
//         fs::create_dir(output_dir).expect("Failed to create bin_output directory");
//     }
//
//     // Generate 100 MeasurementReport messages
//     let encoded_messages = generate_multiple_measurement_reports(100);
//
//     // Save messages to files
//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("{}/measurement_report_{}.bin", output_dir, index + 1);
//         fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// }




// use asnfuzz_rrc_uper::rrc_reconf_comp_entropic::generate_multiple_rrc_reconfig_completes;
// use std::fs;
// use std::path::Path;
//
// fn main() {
//     let output_dir = "./bin_output/rrc_reconfig_comp";
//
//     // Ensure the output directory exists
//     if !Path::new(output_dir).exists() {
//         fs::create_dir_all(output_dir).expect("Failed to create bin_output/rrc_reconfig_complete directory");
//     }
//
//     // Generate 100 RRCReconfigurationComplete messages
//     let encoded_messages = generate_multiple_rrc_reconfig_completes(100);
//
//     // Save messages to files
//     for (index, encoded_message) in encoded_messages.iter().enumerate() {
//         let filename = format!("{}/rrc_reconfig_complete_{}.bin", output_dir, index + 1);
//         fs::write(&filename, encoded_message).expect("Unable to write file");
//         println!("Encoded message saved to {}", filename);
//     }
// }

// use asnfuzz_rrc_uper::generate_rrc_smc_json;
// fn main() {
//     let encoded_message = generate_rrc_smc_json::generate_security_mode_command_json();
//     std::fs::write("bin_output/rrc_smc_exp/wrapped_security_mode_command.bin", encoded_message)
//         .expect("Unable to write file");
//     println!("Encoded message saved to wrapped_security_mode_command.bin");
// } // -> generate_rrc_messages.rs

// use asnfuzz_rrc_uper::generate_batch_rrc_smc_from_json;
// fn main() {
//     // Top-level folder to hold all output
//     let top_output_folder = "bin_output/rrc_smc_exp";
//     // Create if it doesn't exist
//     std::fs::create_dir_all(top_output_folder)
//         .expect("Unable to create top-level rrc_smc_exp folder");
//
//     // We have 9 functions: generate_security_mode_command_1 .. _9
//     // We'll call each function 10 times and put them in a subfolder like:
//     //   bin_output/rrc_smc_exp/security_mode_command_1/1.bin
//     //   bin_output/rrc_smc_exp/security_mode_command_1/2.bin
//     //   ...
//     //   bin_output/rrc_smc_exp/security_mode_command_1/10.bin
//     // Then repeat for security_mode_command_2, etc.
//
//     for i in 1..=9 {
//         // Create a subfolder for each security_mode_command_i
//         let subfolder = format!("{}/security_mode_command_{}", top_output_folder, i);
//         std::fs::create_dir_all(&subfolder)
//             .unwrap_or_else(|_| panic!("Unable to create folder: {}", subfolder));
//
//         // Generate 10 encoded messages for each function
//         for j in 1..=10 {
//             let encoded_message = match i {
//                 1 => generate_batch_rrc_smc_from_json::generate_security_mode_command_1(),
//                 2 => generate_batch_rrc_smc_from_json::generate_security_mode_command_2(),
//                 3 => generate_batch_rrc_smc_from_json::generate_security_mode_command_3(),
//                 4 => generate_batch_rrc_smc_from_json::generate_security_mode_command_4(),
//                 5 => generate_batch_rrc_smc_from_json::generate_security_mode_command_5(),
//                 6 => generate_batch_rrc_smc_from_json::generate_security_mode_command_6(),
//                 7 => generate_batch_rrc_smc_from_json::generate_security_mode_command_7(),
//                 8 => generate_batch_rrc_smc_from_json::generate_security_mode_command_8(),
//                 9 => generate_batch_rrc_smc_from_json::generate_security_mode_command_9(),
//                 _ => unreachable!(),
//             };
//
//             // Build the .bin filename (1.bin, 2.bin, etc.)
//             let bin_path = format!("{}/{}.bin", subfolder, j);
//             std::fs::write(&bin_path, encoded_message)
//                 .unwrap_or_else(|_| panic!("Unable to write file: {}", bin_path));
//         }
//
//         println!(
//             "Encoded 10 messages for security_mode_command_{} stored in '{}'",
//             i, subfolder
//         );
//     }
//
//     println!("All security_mode_command encoded messages generated successfully!");
// } //generate_batch_rrc_smc_from_json.rs


// use asnfuzz_rrc_uper::generate_batch_rrc_sm_fail_from_json;  // Updated import
//
// fn main() {
//     // Top-level folder to hold all output
//     let top_output_folder = "bin_output/rrc_smf_exp";
//     // Create it if it doesn't exist
//     std::fs::create_dir_all(top_output_folder)
//         .expect("Unable to create top-level rrc_smf_exp folder");
//
//     // We have 5 functions: generate_security_mode_failure_1 .. _5
//     // We'll call each function 10 times and put them in a subfolder like:
//     //   bin_output/rrc_smf_exp/security_mode_failure_1/1.bin
//     //   bin_output/rrc_smf_exp/security_mode_failure_1/2.bin
//     //   ...
//     //   bin_output/rrc_smf_exp/security_mode_failure_1/10.bin
//     // Then repeat for security_mode_failure_2, etc.
//
//     for i in 1..=5 {
//         // Create a subfolder for each security_mode_failure_i
//         let subfolder = format!("{}/security_mode_failure_{}", top_output_folder, i);
//         std::fs::create_dir_all(&subfolder)
//             .unwrap_or_else(|_| panic!("Unable to create folder: {}", subfolder));
//
//         // Generate 10 encoded messages for each function
//         for j in 1..=10 {
//             let encoded_message = match i {
//                 1 => generate_batch_rrc_sm_fail_from_json::generate_security_mode_failure_1(),
//                 2 => generate_batch_rrc_sm_fail_from_json::generate_security_mode_failure_2(),
//                 3 => generate_batch_rrc_sm_fail_from_json::generate_security_mode_failure_3(),
//                 4 => generate_batch_rrc_sm_fail_from_json::generate_security_mode_failure_4(),
//                 5 => generate_batch_rrc_sm_fail_from_json::generate_security_mode_failure_5(),
//                 _ => unreachable!(),
//             };
//
//             // Build the .bin filename (1.bin, 2.bin, etc.)
//             let bin_path = format!("{}/{}.bin", subfolder, j);
//             std::fs::write(&bin_path, encoded_message)
//                 .unwrap_or_else(|_| panic!("Unable to write file: {}", bin_path));
//         }
//
//         println!(
//             "Encoded 10 messages for security_mode_failure_{} stored in '{}'",
//             i, subfolder
//         );
//     }
//
//     println!("All security_mode_failure messages generated successfully!");
// } //generate_batch_rrc_sm_fail_from_json.rs

// use asnfuzz_rrc_uper::generate_batch_rrc_smcomp_from_json;  // <-- Updated import
//
// fn main() {
//     // Top-level folder to hold all output
//     let top_output_folder = "bin_output/rrc_smcomp_exp";
//     // Create it if it doesn't exist
//     std::fs::create_dir_all(top_output_folder)
//         .expect("Unable to create top-level rrc_smcomp_exp folder");
//
//     // We have 5 functions: generate_security_mode_complete_1 .. _5
//     // We'll call each function 10 times and put them in a subfolder like:
//     //   bin_output/rrc_smcomp_exp/security_mode_complete_1/1.bin
//     //   bin_output/rrc_smcomp_exp/security_mode_complete_1/2.bin
//     //   ...
//     //   bin_output/rrc_smcomp_exp/security_mode_complete_1/10.bin
//     // Then repeat for security_mode_complete_2, etc.
//
//     for i in 1..=5 {
//         // Create a subfolder for each security_mode_complete_i
//         let subfolder = format!("{}/security_mode_complete_{}", top_output_folder, i);
//         std::fs::create_dir_all(&subfolder)
//             .unwrap_or_else(|_| panic!("Unable to create folder: {}", subfolder));
//
//         // Generate 10 encoded messages for each function
//         for j in 1..=10 {
//             let encoded_message = match i {
//                 1 => generate_batch_rrc_smcomp_from_json::generate_security_mode_complete_1(),
//                 2 => generate_batch_rrc_smcomp_from_json::generate_security_mode_complete_2(),
//                 3 => generate_batch_rrc_smcomp_from_json::generate_security_mode_complete_3(),
//                 4 => generate_batch_rrc_smcomp_from_json::generate_security_mode_complete_4(),
//                 5 => generate_batch_rrc_smcomp_from_json::generate_security_mode_complete_5(),
//                 _ => unreachable!(),
//             };
//
//             // Build the .bin filename (1.bin, 2.bin, etc.)
//             let bin_path = format!("{}/{}.bin", subfolder, j);
//             std::fs::write(&bin_path, encoded_message)
//                 .unwrap_or_else(|_| panic!("Unable to write file: {}", bin_path));
//         }
//
//         println!(
//             "Encoded 10 messages for security_mode_complete_{} stored in '{}'",
//             i, subfolder
//         );
//     }
//
//     println!("All security_mode_complete messages generated successfully!");
// } // generate_batch_rrc_smcomp_from_json.rs

//use asnfuzz_rrc_uper::generate_batch_ue_cap_info_from_json; // <-- Updated import

fn main() {
    // Top-level folder to hold all output
    /*let top_output_folder = "bin_output/rrc_ueci_exp";
    // Create it if it doesn't exist
    std::fs::create_dir_all(top_output_folder)
        .expect("Unable to create top-level rrc_ueci_exp folder");

    // We have 9 functions: generate_UECapabilityInformation_1 .. _9
    // We'll call each function 10 times and put them in a subfolder like:
    //   bin_output/rrc_ueci_exp/ue_capability_information_1/1.bin
    //   bin_output/rrc_ueci_exp/ue_capability_information_1/2.bin
    //   ...
    //   bin_output/rrc_ueci_exp/ue_capability_information_1/10.bin
    // Then repeat for ue_capability_information_2, etc.

    for i in 1..=9 {
        // Create a subfolder for each ue_capability_information_i
        let subfolder = format!("{}/ue_capability_information_{}", top_output_folder, i);
        std::fs::create_dir_all(&subfolder)
            .unwrap_or_else(|_| panic!("Unable to create folder: {}", subfolder));

        // Generate 10 encoded messages for each function
        for j in 1..=10 {
            let encoded_message = match i {
                1 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_1(),
                2 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_2(),
                3 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_3(),
                4 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_4(),
                5 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_5(),
                6 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_6(),
                7 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_7(),
                8 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_8(),
                9 => generate_batch_ue_cap_info_from_json::generate_UECapabilityInformation_9(),
                _ => unreachable!(),
            };

            // Build the .bin filename (1.bin, 2.bin, etc.)
            let bin_path = format!("{}/{}.bin", subfolder, j);
            std::fs::write(&bin_path, encoded_message)
                .unwrap_or_else(|_| panic!("Unable to write file: {}", bin_path));
        }

        println!(
            "Encoded 10 messages for ue_capability_information_{} stored in '{}'",
            i, subfolder
        );
    }
*/
    println!("All ue_capability_information messages generated successfully!");
}




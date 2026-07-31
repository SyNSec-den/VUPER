use crate::rrc::*;
use asnfuzzgen_codecs::uper::UperCodec;

// Implement Clone and Copy for CipheringAlgorithm
impl Clone for CipheringAlgorithm {
    fn clone(&self) -> Self {
        CipheringAlgorithm(self.0)
    }
}

impl Copy for CipheringAlgorithm {}

// Implement Clone and Copy for IntegrityProtAlgorithm
impl Clone for IntegrityProtAlgorithm {
    fn clone(&self) -> Self {
        IntegrityProtAlgorithm(self.0)
    }
}

impl Copy for IntegrityProtAlgorithm {}

// Implement Clone and Copy for RRC_TransactionIdentifier
impl Clone for RRC_TransactionIdentifier {
    fn clone(&self) -> Self {
        RRC_TransactionIdentifier(self.0)
    }
}

impl Copy for RRC_TransactionIdentifier {}


pub fn generate_security_mode_command_variants() -> Vec<Vec<u8>> {
    let mut encoded_messages = Vec::new();

    // Possible values for ciphering_algorithm
    let ciphering_algorithms = vec![
        CipheringAlgorithm(CipheringAlgorithm::NEA0),
        CipheringAlgorithm(CipheringAlgorithm::NEA1),
        CipheringAlgorithm(CipheringAlgorithm::NEA2),
        CipheringAlgorithm(CipheringAlgorithm::NEA3),
    ];

    // Possible values for integrity_prot_algorithm
    let integrity_prot_algorithms = vec![
        Some(IntegrityProtAlgorithm(IntegrityProtAlgorithm::NIA0)),
        Some(IntegrityProtAlgorithm(IntegrityProtAlgorithm::NIA1)),
        Some(IntegrityProtAlgorithm(IntegrityProtAlgorithm::NIA2)),
        Some(IntegrityProtAlgorithm(IntegrityProtAlgorithm::NIA3)),
    ];

    // Possible values for rrc_transaction_identifier
    let rrc_transaction_identifiers = vec![
        RRC_TransactionIdentifier(0),
        RRC_TransactionIdentifier(1),
        RRC_TransactionIdentifier(2),
        RRC_TransactionIdentifier(3),
    ];

    // Iterate over values directly since they implement Copy
    for &ciphering_algorithm in &ciphering_algorithms {
        for &integrity_prot_algorithm in &integrity_prot_algorithms {
            for &rrc_transaction_identifier in &rrc_transaction_identifiers {
                // Construct SecurityAlgorithmConfig with varying values
                let security_algorithm_config = SecurityAlgorithmConfig {
                    ciphering_algorithm,
                    integrity_prot_algorithm,
                };

                // Construct SecurityConfigSMC using the SecurityAlgorithmConfig instance
                let security_config_smc = SecurityConfigSMC {
                    security_algorithm_config,
                };


                // Construct the SecurityModeCommand_IEs
                let security_mode_command_ies = SecurityModeCommand_IEs {
                    security_config_smc,
                    late_non_critical_extension: None, 
                    non_critical_extension: None,      
                };

                // Create the SecurityModeCommand structure
                let security_mode_command = SecurityModeCommand {
                    rrc_transaction_identifier,
                    critical_extensions: SecurityModeCommandCriticalExtensions::SecurityModeCommand(
                        security_mode_command_ies,
                    ),
                };

                // Wrap the SecurityModeCommand in DL-DCCH-Message
                let dl_dcch_message = DL_DCCH_Message {
                    message: DL_DCCH_MessageType::C1(DL_DCCH_MessageType_c1::SecurityModeCommand(
                        security_mode_command,
                    )),
                };

                // Encode the DL-DCCH-Message using UPER
                let mut codec_data = asnfuzzgen_codecs::PerCodecData::new_uper();
                dl_dcch_message.uper_encode(&mut codec_data).unwrap();
                let encoded_bytes = codec_data.into_bytes();

                // Add the encoded message to the list
                encoded_messages.push(encoded_bytes);
            }
        }
    }

    encoded_messages
}
import os

def read_bin_to_hex(file_path):
    try:
        with open(file_path, 'rb') as file:
            binary_data = file.read()
            hex_data = binary_data.hex()
            return hex_data
    except FileNotFoundError:
        print(f"File {file_path} not found. Please check the file path.")
        return None

def process_folder(folder_path, output_file):
    with open(output_file, 'w') as outfile:
        for filename in os.listdir(folder_path):
            if filename.endswith('.bin'):
                file_path = os.path.join(folder_path, filename)
                hex_content = read_bin_to_hex(file_path)
                if hex_content:
                    outfile.write(f"{hex_content}\n")
                else:
                    print(f"Could not read {filename} as hex.")

# Usage
# folder_path = './bin_output/rrc_reest_req'
folder_path = 'bin_output/rrc_smc_exp'
output_file = './output.txt'
process_folder(folder_path, output_file)

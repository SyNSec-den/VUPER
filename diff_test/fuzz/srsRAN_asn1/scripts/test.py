#!/usr/bin/env python3
import os
import re
import subprocess

def natural_sort_key(s):
    """
    Create a sort key that approximates "natural order" where numbers in strings are compared
    numerically. This is similar to how ls -v sorts file names.
    """
    return [int(text) if text.isdigit() else text.lower() for text in re.split('([0-9]+)', s)]

def main():
    # Define the directory containing the queue files
    input_dir = "../../asn1c_test/output_dir/ul/testrun1/default/queue/"
    
    # List all files in the directory
    try:
        files = os.listdir(input_dir)
    except Exception as e:
        print(f"Error listing directory {input_dir}: {e}")
        return
    
    # Sort the file names in natural (version) order similar to "ls -v"
    files.sort(key=natural_sort_key)
    
    # Select files to process
    files_to_process = files[1000:2000]
    
    # Process each file: read the file and pipe its content into the external test executable.
    for filename in files_to_process:
        file_path = os.path.join(input_dir, filename)
        try:
            with open(file_path, 'rb') as file_obj:
                content = file_obj.read()
        except Exception as e:
            # skip things like a directory
            print(f"Error reading {file_path}: {e}")
            continue
        
        # Run the external test executable and pass the file's content as stdin.
        try:
            result = subprocess.run(
                ["./tests/unittests/asn1/main_test"],
                input=content,
                capture_output=True
            )

            # if the output is not True, then we print which file it is
            output_text = result.stdout.decode("utf-8")
            if (output_text != "True\n"):
                print(f"{filename} : {output_text}")

            # Optionally, you can check result.returncode or capture stdout/stderr if needed.
        except Exception as e:
            print(f"Error running the test on {file_path}: {e}")

if __name__ == "__main__":
    main()

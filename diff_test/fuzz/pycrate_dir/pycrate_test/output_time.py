import nr_test
import os
import time
import sys

def get_all_files(directory):
    """Returns a list of all files (excluding directories) in the given directory."""
    return [
        os.path.join(directory, f)
        for f in os.listdir(directory)
        if os.path.isfile(os.path.join(directory, f))
    ]

def read_file(filename):
    """Reads a file into memory and returns its content."""
    with open(filename, "rb") as f:
        return f.read()

def measure_total_parsing_time(directory):
    """Measures total parsing time for all files in a directory, excluding I/O."""
    file_list = get_all_files(directory)
    total_time = 0.0

    sys.stdout = open('/dev/null', 'w')  # Disable printing
    bad_input = 0
    total_input = 0

    for filename in file_list:
        total_input += 1
        content = read_file(filename)  # Load file into memory first

        start_time = time.perf_counter()  # Start timing
        dl_dcch = nr_test.NR_RRC_Definitions.DL_DCCH_Message
        try:
            #sys.stdout = open(os.devnull, 'w')
            dl_dcch.from_uper(content)
            #print(dl_dcch())
            #//sys.stdout = sys.__stdout__
        except:
            bad_input += 1
        
        end_time = time.perf_counter()  # End timing

        total_time += (end_time - start_time)

    sys.stdout = sys.__stdout__  # Restore stdout

    print(f"Total input is: {total_input}, bad input is {bad_input}")
    print(f"Total parsing time for {len(file_list)} files: {total_time:.6f} seconds")

# Example parser function (replace with your actual parser)
def dummy_parser(content):
    """Simulate a parsing function (replace with your real parser)."""
    pass  # Your actual parsing logic goes here

if __name__ == "__main__":
    directory = "/home/zhouxt/Documents/parse/messages_result/testrun1_pycrate/correct"  # Replace with the actual directory path
    measure_total_parsing_time(directory)

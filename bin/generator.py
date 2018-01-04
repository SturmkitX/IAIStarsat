import sys

def help():
    msg = """
    Usage: python generator.py <K> <output_file_base>
    """
    print(msg)

def print_base(k_num, file_path):
    with open(file_path, "w") as fileout:
        fileout.write("(AND\n")

        # rule 1
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (IMP (NOT C0) (ALL R%d (NOT C0))))\n" % man)
        fileout.write("\n")

        # rule 2
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (ALL R%d (NOT (IMP C0 C%d))))\n" % (man, man))
        fileout.write("\n")

        # rule 3
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (NOT (ALL R%d C%d)))\n" % (man, man))
        fileout.write(")\n")

def print_prove(k_num, file_path):
    with open(file_path, "w") as fileout:
        fileout.write("(AND\n")

        # rule 1
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (IMP (NOT C0) (ALL R%d (NOT C0))))\n" % man)
        fileout.write("\n")

        # rule 2
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (ALL R%d (NOT (IMP C0 C%d))))\n" % (man, man))
        fileout.write("\n")

        # rule 3
        for man in range(1, k_num):
            fileout.write("\t(ALL R0 (NOT (ALL R%d C%d)))\n" % (man, man))
        fileout.write("\n")
        fileout.write("\t(NOT (ALL R0 C0))\n")
        fileout.write(")\n")

def main(k_num, out_file_path):
    print_base(k_num, out_file_path + ".alc")
    print_prove(k_num, out_file_path + "_prove.alc")


if __name__ == "__main__":
    if len(sys.argv) < 3:
        help()
    else:
        main(int(sys.argv[1]), sys.argv[2])

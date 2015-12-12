#!/usr/bin/env python

import os
import sys
import getopt
import string
import subprocess as sp
import tempfile

cpp_EXTENSIONS = ['cpp', 'cc', 'C', 'cxx']
c_EXTENSIONS = ['c']
object_EXTENSIONS = ['o', 'a', 'la']
archive_EXTENSIONS = ['a', 'la']

## could add a switch to control these
compileOrig = False
outputCpp = False
compressIR = False 

compile_frontend = None
protean_pass_path = None
protean_rt_path = None

def file_exists(name):
    if os.path.isfile(name):
        return True
    return False

def err_out(msg):
    sys.stderr.write(str(msg) + '\n')

def error_die(msg=''):
    if msg != '':
        err_out('error: ' + msg)
    sys.exit(1)

def print_usage(err=''):
    if err != '':
        err_out('error: ' + str(err))
    err_out('usage: ' + sys.argv[0])
    err_out('\t-c\tcompile to object files')
    err_out('\t-o\toutput file name')
    err_out('example: ' + sys.argv[0] + ' -c -o hello.o hello.c')
    err_out('example: ' + sys.argv[0] + ' -o hello hello.o')
    error_die()


def verify_env():
    global compile_frontend, protean_pass_path, protean_rt_path

    fe = os.getenv('PROTEAN_COMPILE_FRONTEND')
    if fe == None:
        error_die('PROTEAN_COMPILE_FRONTEND is not set. You should not call this script directly. Instead, use pcc or pc++.')

    protean_path = os.getenv('PROTEAN_PATH')
    if protean_path == None:
        error_die('PROTEAN_PATH is not set. See env.sh included with the protean code distribution for help setting it.')

    protean_rt_path = protean_path + '/runtime/'

    llvm_path = os.getenv('LLVM_PATH')
    if llvm_path == None:
        error_die('LLVM_PATH is not set. See env.sh included with the protean code distribution for help setting it.')

    llvm_build = os.getenv('LLVM_BUILD')
    if llvm_build == None:
        error_die('LLVM_BUILD is not set. See env.sh included with the protean code distribution for help setting it.')

    protean_pass_path = llvm_path + '/' + llvm_build + '/lib'
    compile_frontend = llvm_path + '/' + llvm_build + '/bin/' + fe

    print protean_pass_path


def get_language(fname, allowed):
    for l in allowed:
        extlist = eval(l + '_EXTENSIONS')
        for ext in extlist:
            if fname.endswith('.' + ext):
                return ext, l

    error_die('expected file with one of the following types: ' + str(allowed) + ', got ' + str(fname))


def run_shell_command(cmd):
    toks = cmd.split()
    print '***** invoking shell: ' + str(string.join(toks, ' '))

    # call command and capture stdout
    tmpfname = tempfile.mktemp()
    tmpf = open(tmpfname, 'w')
    res = sp.call(toks, stdout=tmpf)
    tmpf.close()

    if res != 0:
        error_die('error code ' + str(res) + ' while executing shell command: ' + str(toks))

    # read stdout back in
    tmpf = open(tmpfname, 'r')
    d = tmpf.readlines()
    tmpf.close()

    # remove tmp file, return contents of stdout
    os.remove(tmpfname)
    return d


def strip_ext(fname, ext):
    if not fname.endswith('.' + ext):
        error_die('expecting file ' + str(fname) + ' to end with .' + str(ext))
    return fname[0:len(fname)-len(ext)-1]

def get_outfile(fname, ext, outFile, newext):
    ret = outFile
    if outFile == "":
# FIXME
#        ret = os.path.basename(strip_ext(fname, ext) + '.' + newext)
        ret = strip_ext(fname, ext) + '.' + newext
    return ret    

def compile_cpp(fname, ext, outFile, ptopts):
    print '=========== COMPILING C++ SOURCE FILE ' + fname + ' ============='

    bytecode = get_outfile(fname, ext, outFile, 'o')
    mystr = {'SRC': fname, 'BC': bytecode, 'OPTS': string.join(ptopts, ' ')}

    run_shell_command(compile_frontend + ' %(OPTS)s -emit-llvm -c %(SRC)s -o %(BC)s' % mystr)
    if outputCpp == True:
        run_shell_command('llc -march=cpp %(BC)s -o %(BC)s.ir' % mystr)

    return bytecode

def compile_c(fname, ext, outFile, ptopts):
    print '=========== COMPILING C SOURCE FILE ' + fname + ' ============='

    bytecode = get_outfile(fname, ext, outFile, 'o')
    mystr = {'SRC': fname, 'BC': bytecode, 'OPTS': string.join(ptopts, ' ')}

    run_shell_command(compile_frontend + ' %(OPTS)s -emit-llvm -c %(SRC)s -o %(BC)s' % mystr)
    if outputCpp == True:
        run_shell_command('llc -march=cpp %(BC)s -o %(BC)s.ir' % mystr)

    return bytecode

def link_files(fnames, outFile, ptopts):
    print '=========== LINKING OBJECT FILES ============='
    bytecodes = []
    archives = []

    if len(fnames) == 1:
        bytecodes.append(fnames[0])
    else:
        for fname in fnames:
            # order matters on this list!
            ext, lang = get_language(fname, ['archive', 'object'])
            if lang == 'object':
                bytecodes.append(fname.strip())
            else:
                archives.append(fname.strip())

    # FIXME: this is brittle. what we really need to do is resolve linker paths to find **all** libraries, resolve LLVM archives
    # here, then pass though the unpacked LLVM objects to llvm-link while reserving the real objects for the final clang link.
    for a in archives:
        continue
        myout = run_shell_command('ar t ' + a)
        print myout
        for line in myout:
            bytecodes.append(line.strip())
        run_shell_command('ar x ' + a)

    mystr = {'UNIF': outFile, 'OBJS': string.join(bytecodes, ' '), 'protean_pass_path': protean_pass_path, 'protean_rt_path': protean_rt_path, 'OPTS': string.join(ptopts, ' '), 'ARCV': string.join(archives, ' ')}

    run_shell_command('llvm-link -o %(UNIF)s.bc %(OBJS)s' % mystr)
    if compileOrig == False:
#        run_shell_command('opt -load %(protean_pass_path)s/protean_pass.so -protean -o %(UNIF)s.protean.bc %(UNIF)s.bc' % mystr)
        run_shell_command('opt -load %(protean_pass_path)s/protean_pass.so -protean -always-inline -o %(UNIF)s.protean.bc %(UNIF)s.bc %(OPTS)s' % mystr)
    else:
        run_shell_command('cp %(UNIF)s.bc %(UNIF)s.protean.bc' % mystr)
    run_shell_command('llc -filetype=obj %(UNIF)s.protean.bc -o %(UNIF)s.o' % mystr)
    # FIXME: probably don't need export-dynamic any more
    run_shell_command(compile_frontend + ' %(OPTS)s %(UNIF)s.o %(ARCV)s -o %(UNIF)s.protean.nobc -L%(protean_rt_path)s -lprotean_rt -ldl -lrt -Wl,--export-dynamic' % mystr)
    if compressIR == False:
        run_shell_command('objcopy --add-section .protean_ir=%(UNIF)s.protean.bc %(UNIF)s.protean.nobc %(UNIF)s' % mystr)
    else:
        run_shell_command('gzip %(UNIF)s.protean.bc' % mystr)
        run_shell_command('objcopy --add-section .protean_ir.gz=%(UNIF)s.protean.bc.gz %(UNIF)s.protean.nobc %(UNIF)s' % mystr)


def main():
    verify_env()

    if len(sys.argv) < 2:
        print_usage()

    toObject = False
    outFile = ''

    args = []
    skip = False
    for i in range(1, len(sys.argv), 1):
        if sys.argv[i] == '-c':
            toObject = True
            skip = False
        elif sys.argv[i] == '-o':
            if len(sys.argv) == i+1:
                error_die('-o option requires argument')
            outFile = sys.argv[i+1]
            skip = True
        else:
            if skip == False:
                args.append(sys.argv[i])
            skip = False

    ptopts = []
    fnames = []
    for a in args:
        if a.startswith('-'):
            ptopts.append(a)
        else:
            fnames.append(a)

    if toObject == True:
        if len(fnames) != 1:
            error_die('with -c supply exactly 1 input file: ' + str(fnames))
        if outFile == '':
            fname = fnames[0]
            ext, lang = get_language(fname, ['cpp', 'c'])
            outFile = strip_ext(fname, ext) + '.o'


    if len(fnames) < 1:
        if (sys.argv[1] == '--version'):
            run_shell_command('clang --version')
            sys.exit(0)
        else:
            error_die('this script requires files to be passed: ' + str(string.join(sys.argv)))

    link_these = []
    for fname in fnames:
        ext, lang = get_language(fname, ['cpp', 'c', 'object'])
        if lang == 'object':
            link_these.append(fname)
        else:
            link_these.append(eval('compile_' + lang + '(fname, ext, outFile, ptopts)'))

    if toObject == False:
        if outFile == '':
            outFile = 'a.out'
        link_files(link_these, outFile, ptopts)


if __name__ == '__main__':
    main()

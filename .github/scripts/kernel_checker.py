#!/usr/bin/env python3

import os
from common.header_checker import HeaderChecker

#--------------------------------------------------------------------------------------------------
#                                            CONFIG
#--------------------------------------------------------------------------------------------------
KERNEL_IGNORED_FILES = [
    'FreeRTOS-openocd.c'
]

KERNEL_IGNORED_EXTENSIONS = [
    '.yml',
    '.css',
    '.idx',
    '.md',
    '.url',
    '.sty',
    '.0-rc2',
    '.s82',
    '.js',
    '.out',
    '.pack',
    '.2',
    '.1-kernel-only',
    '.0-kernel-only',
    '.0-rc1',
    '.readme',
    '.tex',
    '.png',
    '.bat',
    '.sh',
    '.txt'
]

KERNEL_IGNORED_PATTERNS = [
    r'.*\.git.*',
    r'.*portable/ThirdParty/GCC/Posix/port*',
    r'.*portable.*Xtensa_ESP32\/include\/portmacro\.h',
    r'.*portable.*CDK\/T-HEAD_CK802\/portmacro\.h',
    r'.*portable.*GCC\/Posix\/portmacro\.h',
    r'.*portable.*Xtensa_ESP32.*port\.c',
    r'.*portable.*Xtensa_ESP32.*portasm\.S',
    r'.*portable.*Xtensa_ESP32.*xtensa_.*',
    r'.*portable.*Xtensa_ESP32.*portmux_impl.*',
    r'.*portable.*Xtensa_ESP32.*xt_asm_utils\.h'
]

KERNEL_HEADER = [
    '/*\n',
    ' * FreeRTOS Kernel V10.4.3\n',
    ' * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.\n',
    ' *\n',
    ' * Permission is hereby granted, free of charge, to any person obtaining a copy of\n',
    ' * this software and associated documentation files (the "Software"), to deal in\n',
    ' * the Software without restriction, including without limitation the rights to\n',
    ' * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of\n',
    ' * the Software, and to permit persons to whom the Software is furnished to do so,\n',
    ' * subject to the following conditions:\n',
    ' *\n',
    ' * The above copyright notice and this permission notice shall be included in all\n',
    ' * copies or substantial portions of the Software.\n',
    ' *\n',
    ' * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR\n',
    ' * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS\n',
    ' * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR\n',
    ' * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER\n',
    ' * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN\n',
    ' * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.\n',
    ' *\n',
    ' * https://www.FreeRTOS.org\n',
    ' * https://github.com/FreeRTOS\n',
    ' *\n',
    ' */\n',
]


def main():
    parser = HeaderChecker.configArgParser()
    args   = parser.parse_args()

    # Configure the checks then run
    checker = HeaderChecker(KERNEL_HEADER)
    checker.ignoreExtension(*KERNEL_IGNORED_EXTENSIONS)
    checker.ignorePattern(*KERNEL_IGNORED_PATTERNS)
    checker.ignoreFile(*KERNEL_IGNORED_FILES)
    checker.ignoreFile(os.path.split(__file__)[-1])

    rc = checker.processArgs(args)
    if rc:
        checker.showHelp(__file__)

    return rc

if __name__ == '__main__':
    exit(main())


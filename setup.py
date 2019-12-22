#!/usr/bin/env python
import versioneer

from os.path import exists
from setuptools import setup

setup(
    name="miniKanren",
    version=versioneer.get_version(),
    cmdclass=versioneer.get_cmdclass(),
    description="Relational programming in Python",
    url="http://github.com/pythological/kanren",
    maintainer="Brandon T. Willard",
    maintainer_email="brandonwillard+kanren@gmail.com",
    license="BSD",
    packages=["kanren"],
    install_requires=["toolz", "cons", "multipledispatch", "logical-unification",],
    tests_require=["pytest", "sympy"],
    long_description=open("README.md").read() if exists("README.md") else "",
    long_description_content_type="text/markdown",
    zip_safe=False,
    python_requires=">=3.6",
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "License :: OSI Approved :: BSD License",
        "Programming Language :: Python",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.6",
        "Programming Language :: Python :: 3.7",
        "Programming Language :: Python :: Implementation :: CPython",
        "Programming Language :: Python :: Implementation :: PyPy",
    ],
)

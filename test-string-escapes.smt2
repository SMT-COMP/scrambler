(set-info :smt-lib-version 2.6)
(set-info :echo "The only string escape in version 2.6 is "" for a double quote character.")
(set-info :echo "Notably, backslash+double quote (\"") and backslash+backslash (\\) are no longer escapes.")
(set-info :echo "Some edge cases for testing:")
(set-info :echo "")
(set-info :echo "\")
(set-info :echo "\\")
(set-info :echo "\\\")
(set-info :echo """")
(set-info :echo "\""")
(set-info :echo "\\""")
(set-info :echo "\\\""")
(set-info :echo """\")
(set-info :echo """\\")
(set-info :echo """\\\")
(set-info :echo "
")
(set-info :echo "\
")
(set-info :echo "\\
")
(set-info :echo "\\\
")
(set-info :echo "
\")
(set-info :echo "
\\")
(set-info :echo "
\\\")
(set-info :echo """
")
(set-info :echo "
""")
(set-info :echo "\
""")
(set-info :echo "\\
""")
(set-info :echo "\\\
""")
(set-info :echo """
\")
(set-info :echo """
\\")
(set-info :echo """
\\\")
(set-logic ALL)
(check-sat)
(exit)

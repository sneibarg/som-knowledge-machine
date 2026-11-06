;;; KM - The Knowledge Machine - Build Date:  Sat, Nov 07, 2015 12:51:02 PM
#|
======================================================================
	 KM - THE KNOWLEDGE MACHINE - INFERENCE ENGINE 2.5.45
======================================================================

This software is released under the Simplified BSD Licence (below). If you would like a
copy of this software issued under a different license please contact the authors.

======================================================================

Copyright (c) 1994-2015 Peter Clark and Bruce Porter. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, this list of
      conditions and the following disclaimer.

   2. Redistributions in binary form must reproduce the above copyright notice, this list
      of conditions and the following disclaimer in the documentation and/or other materials
      provided with the distribution.

THIS SOFTWARE IS PROVIDED BY PETER CLARK AND BRUCE PORTER ``AS IS'' AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL PETER CLARK AND BRUCE PORTER OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those of the
authors and should not be interpreted as representing official policies, either expressed
or implied, of Peter Clark and Bruce Porter.

Contact information:
Peter Clark (peterc@allenai.org)
Bruce Porter (porter@cs.utexas.edu)

======================================================================

The source code, manuals, and a test suite of examples for the most
recent version of KM are available at

	http://www.cs.utexas.edu/users/mfkb/km/

Check this site for RELEASE NOTES and the CURRENT VERSION of KM.

======================================================================
		USING THIS FILE:
======================================================================

Save this file as (say) km.lisp, then load it into your favorite Lisp
environment:
	% lisp
	> (load "km")

For greatly increased efficiency, make a compiled version of this file:
	% lisp
	> (compile-file "km")
	> (load "km")
will load the faster, compiled version in future.

[Note: you no longer need to pre-load km.lisp before compiling,
 as described in the manual]

To start the query interpreter running, type (km):
	> (km)
	KM>

See the User Manual and Reference Manual for instructions on using KM,
and building knowledge bases. The manuals are available at:

	http://www.cs.utexas.edu/users/mfkb/km/

======================================================================
		READING/EDITING THE SOURCE:
======================================================================

The following file is a machine-built concatenation of the various files
in the KM inference system. It can be loaded or compiled directly into
Lisp, deconcatenation is not necessary for running KM.

Although you can read/edit the below code all in this one file, it is
very large and unweildy; you may prefer to break it up into the
(approx 20) constituent files which it comprises. You can break it up
either manually, looking for the ";;; FILE: <file>" headers
below which denote the start of different files in this concatenation,
OR use the Perl unpacker below which automatically cut this big file
into its consistutent files.

Peter Clark
peterc@allenai.org

======================================================================
	DISASSEMBLING THIS CONCATENATION INTO ITS CONSTITUENT FILES:
======================================================================

Note you don't have to disassemble km.lisp to use KM. However, if you
want to read/edit the code, you might find it helpful to break it up into
individual files.

If you do disassmble the files, then the single file loadme.lisp contains
(commented out) load commands to load all the other constituent files, for
your convenience. (Don't forget to uncomment the load commands in this file).

If you don't disassemble the files and just work with km.lisp, then you can
ignore all of this.

Option 1. (For Emacs users)
[Thanks to Joe Corneli for this piece of code!]
[(1) Ignore end-of-line whitespace - thanks to Nate Blaylock]
[(2) Thanks to Dan Tecuci pointing out "-" needs to be the last character in
     the regexp, otherwise it has the meaning of a character range delimeter.]

(save-excursion
  (let ((case-fold-search nil))
    (goto-char (point-min))
;   (while (re-search-forward "^;;; FILE: +\\(.*\\)" nil t) [see (1) above]
;   (while (re-search-forward "^;;; FILE: +\\([a-zA-Z-\\._]+\\)" nil t) [(2)]
    (while (re-search-forward "^;;; FILE: +\\([a-zA-Z\\._-]+\\)" nil t)
      (let* ((matched (match-string 1))
             (beg (match-beginning 0))
             (end (or (save-excursion
                        (when (search-forward-regexp "^;;; FILE: +.*" nil t)
                          (match-beginning 0)))
                      (point-max)))
             (str (buffer-substring beg end)))
          (with-temp-file matched
            (save-excursion (insert str))
            (next-line 1)
; uncomment the below lines if you want KM files to have KM package declaration
            (insert (concat "(unless (find-package :km) (make-package :km :use '(:common-lisp)))\n"
                            "(in-package :km)\n"))
	)))))
             ^ position cursor behind the emacs lisp expression above and
               run M-x eval-last-sexp

Option 2. (For non-Emacs users)

  1. cut and paste the short Perl script below to a file, eg called
	"disassemble"
  2. Make sure the first line is
		#!/usr/local/bin/perl
     and edit this path /usr/local/bin/perl as needed to point to the
	local version of Perl.
  3. Make the file executable:
	% chmod a+x disassemble
  4. Now disassemble km.lisp:
	% disassemble km.lisp

This will populate the current directory with the approx. 20 Lisp files
constituting the KM system.

------------------------------ cut here ------------------------------
#!/usr/local/bin/perl
# Splits file with internal file markers of the form:
# ;;; FILE: <filename>
# into individual files in the current directory.
# Outputs to stdout information about processing.
# require 5.0;
$lineno = 0 ;
if ($#ARGV != 0) { die "Usage: $0 filename.";}	# 1 and only 1 arg
$fn = shift(@ARGV);

open(PACKED, "<$fn") || die "Could not open file $fn\n ";
$_ = <PACKED>; $lineno += 1;	# Read first line, and count it
chop;
($junk, $outfile) = split (/:/);

unless ($junk != /^;;; FILE/o) {
	die "Missing file tag ;;; FILE: Line number $lineno."
}
# Open file for writing

unless (open (OUTFILE, ">$outfile")) {
	die "Could not open file $outfile for writing.";
	}
print "$outfile created\n";
while (<PACKED>) {
	$lineno += 1;
	($junk, $outfile) = split (/:/);
	if ($junk =~ /^;;; FILE/o) {
		close (OUTFILE);
		chop($outfile);
		unless (open (OUTFILE, ">$outfile")) {
	die "Could not open file $outfile for writing.  Line number $lineno.";
		}
		print "$outfile created\n";
# uncomment the below line if you want KM files to have KM package declaration
		print (OUTFILE "\n(unless (find-package :km) (make-package :km :use '(:common-lisp)))\n");
		print (OUTFILE "(in-package :km)\n");
	}
	else {
		print (OUTFILE $_);
	}
}
close(PACKED);
close(OUTFILE);
print "Completed without errors. Processed $lineno lines of input from $fn.\n";
------------------------------ cut here ------------------------------
|#

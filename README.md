Prolog for JCU
==============

This package was developed to demonstrate the ideas behind the Prolog language.
It uses a very small interpreter (*Language.Prolog.Nanoprolog*) which can be
run on its own.

This package contains an environment constructed for the Junior College at
Utrecht University. It provides a simple environment in which rules can be
defined, and proofs can be constructed interactively. The software can be
installed on a server, so students do not have to install anything on their own
machines.


Installation instructions
=========================

This software has been tested with Haskell Platform 2012.4.0.0 on Mac
OS X 10.8.2, GHC 7.4.2 (64-bit), and UHC 1.1.4, revision master@4526152fc7, timestamp 20121116 +0100 125057

To build the JCU application make sure you have the following variables in your
environment `UHC_JSCRIPT`, `UHC_UU_TC` and `UHC_NANOPROLOG`. They should point to the sources of the uhc-js library, the UU Talen & Compiler Parser combinator library and the NanoProlog library respectively.

``` ruby
#! /usr/bin/ruby
require 'readline'

def command?(command)
  system("which #{ command} > /dev/null 2>&1")
end

def library?(lib) 
  system("ghc-pkg list | grep #{lib} > /dev/null 2>&1")
end

def request(question, onYes)
  stty_save = `stty -g`.chomp
  trap('INT') { system('stty', stty_save); exit 1 }

  line = Readline.readline(question, true)

  if line.downcase == "y" || line == ""
    return onYes.call
  end

  return false
  
end

def colorize(text, color_code)
  "#{color_code}#{text}\033[0m"
end

def red(text); colorize(text, "\033[31m"); end
def green(text); colorize(text, "\033[32m"); end
def yellow(text); colorize(text, "\033[33m"); end
def blue(text); colorize(text, "\033[34m"); end

class Message
  def self.ok(message)
    puts("[  #{green("CHECK")}  ] #{message}")
  end 

  def self.error(message)
    puts("[  #{red("FAILED")} ] #{message}")
  end
  
  def self.info(message)
    puts("[  #{yellow("INFO")}   ] #{message}")
  end
  
  def self.question(message)
    puts("[  #{blue("REQ")}    ] #{message}")
  end
end

# Message.ok ""
# Message.error ""
# Message.info ""
# Message.question ""
# exit

def check?(condition, message) 
  if condition
    Message.ok(message)
  else
    Message.error(message)
  end
  condition
end

if ENV['UHC'] == ""
  Message.error "Please provide the $UHC variable before running this script!"
  exit 1
end


requiredCommands = ["git", "ghc", "cabal", "uuagc"]
requiredLibs     = ["uulib", "fgl", "network", "binary"]

cabalInstall = "cabal install --user "

requiredCommands.each { | command | 
  if !check?((command? command), command)
    exit 1
  end
}

requiredLibs.each {|lib|
  command = cabalInstall + lib
  if !check?((library? lib), lib)
    if !request(blue("Install #{lib}? [Y/n]: "), lambda { system command })
      exit 1
    end
    !check?((library? lib), lib)
  end
}


# Check Cabal packages

# Check github projects
projects = {"jcu"        => {:repo => "https://github.com/UU-ComputerScience/JCU", :branch => "standalone"},
            "uhcjs"      => {:repo => "https://github.com/UU-ComputerScience/uhc-js", :branch => "master"},
            "NanoProlog" => {:repo => "https://github.com/UU-ComputerScience/NanoProlog", :branch => "master"}
          }

# Check whether dir exists and if not pull it
projects.each { |key, info|
  Message.info("Checking " + key)
  if File.directory? key
    command = "cd " + key + " && " + "git pull"
  
  else
    command = "git clone #{info[:repo]} #{key} && cd #{key}; git checkout #{info[:branch]}"
  end
  
  if !system command
    exit 1
  end
}        

if !File.directory? "uu-tc-2009.2.2"
  puts "Downloading uu-tc" 
  `curl -L -O http://www.cs.uu.nl/docs/vakken/b3tc/dist/uu-tc-2009.2.2.tar.gz`
  puts "Extracting it"
  `tar xvzf uu-tc-2009.2.2.tar.gz`
else
  Message.ok "uu-tc library already downloaded."
end
           
cwd = Dir.pwd
# CD into the Clientside app and build
Message.info "Please provide the $UHC variable yourself: export UHC=..."
Message.info "You can build UHC-JS with the following command:"
Message.info "    make uhc"
Message.info "Building the client-side "
system "export UHC_JSCRIPT=#{cwd}/uhcjs/uhc-js/src;export UHC_NANOPROLOG=#{cwd}/NanoProlog/src;export UHC_UU_TC=#{cwd}/uu-tc-2009.2.2/src;cd jcu && make"

Message.info "If all went okay you can now cd into the #{yellow "`jcu`"} directory, and open index.html. We will now try doing that just for you."
if command? "open"
  system "open jcu/index.html"
end

```


Usage instructions
==================
Just open the index.html file after you have run `make`.


Using
-----
After logging in, the main screen is visible. It is divided in two sections.
On the left-hand side we have the proof tree and on the right-hand side
the list of rules.
(TODO: Finish this bit)

#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""RootVision - 工具函数"""

import sys
import os
import importlib
import warnings


def check_python_version():
    """检查Python版本兼容性"""
    python_version = sys.version_info
    if python_version < (3, 8):
        print(f"警告: 当前Python版本 {python_version.major}.{python_version.minor}")
        print("建议升级到Python 3.8或更高版本")
    return True


def check_dependencies():
    """检查并导入依赖库，返回缺失的库列表"""
    required_libs = [
        ('opencv-python', 'cv2'),
        ('numpy', 'numpy'),
        ('scikit-image', 'skimage'),
        ('scipy', 'scipy'),
        ('matplotlib', 'matplotlib'),
        ('Pillow', 'PIL'),
        ('psutil', 'psutil'),
    ]

    missing_libs = []
    for pip_name, import_name in required_libs:
        try:
            importlib.import_module(import_name)
        except ImportError:
            missing_libs.append(pip_name)

    warnings.filterwarnings('ignore', category=UserWarning)
    warnings.filterwarnings('ignore', category=FutureWarning)
    warnings.filterwarnings('ignore', category=DeprecationWarning)

    return missing_libs


def get_config_path():
    """返回 config.json 的路径，兼容 PyInstaller --onefile 和开发环境"""
    if getattr(sys, 'frozen', False):
        base_dir = os.path.dirname(sys.executable)
    else:
        base_dir = os.path.dirname(os.path.abspath(__file__))
        # __file__ 在 rootvision/utils.py，上溯到项目根目录
        base_dir = os.path.dirname(base_dir)
    return os.path.join(base_dir, "config.json")
